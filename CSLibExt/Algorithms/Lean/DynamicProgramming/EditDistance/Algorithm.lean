/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Script

/-!
# Unit-cost Levenshtein distance

Bottom-up prefix dynamic programming with deterministic script reconstruction. The recurrence and
boundary conditions follow Wagner and Fischer. Equal minima choose diagonal, then deletion, then
insertion.
-/

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

private def referenceDistance [BEq α] : List α → List α → Nat
  | [], target => target.length
  | source, [] => source.length
  | sourceValue :: source, targetValue :: target =>
      min (referenceDistance source target +
        if sourceValue == targetValue then 0 else 1)
        (min (referenceDistance source (targetValue :: target) + 1)
          (referenceDistance (sourceValue :: source) target + 1))
termination_by source target => source.length + target.length

private lemma referenceDistance_nil_right [BEq α] (source : List α) :
    referenceDistance source [] = source.length := by
  cases source <;> simp [referenceDistance]

/-- Compute unit-cost edit distance and one deterministic minimum-cost script. -/
public def editDistance {α : Type u} [BEq α] (source target : List α) :
    TimeM EditDistanceCost (EditDistanceResult α) :=
  let diagonalCost (sourceValue targetValue : α) : Nat :=
    if sourceValue == targetValue then 0 else 1
  let diagonalStep (sourceValue targetValue : α) : EditStep α :=
    if sourceValue == targetValue then .keep sourceValue else .substitute sourceValue targetValue
  let Row (n : Nat) : Type u :=
    ULift.{u} (Subtype (fun row : Array Nat => row.size = n + 1))
  let rec @[reducible] buildInitialRow (n : Nat) :
      (j : Nat) → j ≤ n → TimeM EditDistanceCost (Row j)
    | 0, _ => do
        TimeM.tick ⟨1, 0⟩
        pure ⟨⟨#[0], by simp⟩⟩
    | j + 1, hj => do
        let row ← buildInitialRow n j (by omega)
        TimeM.tick ⟨1, 0⟩
        pure ⟨⟨row.down.1.push (j + 1), by simp [row.down.2]⟩⟩
  let rec @[reducible] buildRow (sourceValue : α) (target : Array α)
      (up : Row target.size) (first : Nat) :
      (j : Nat) → j ≤ target.size → TimeM EditDistanceCost (Row j)
    | 0, _ => do
        TimeM.tick ⟨1, 0⟩
        pure ⟨⟨#[first], by simp⟩⟩
    | j + 1, hj => do
        let row ← buildRow sourceValue target up first j (by omega)
        TimeM.tick ⟨1, 0⟩
        let diagonal := up.down.1[j]'(by rw [up.down.2]; omega) +
          if sourceValue == target[j] then 0 else 1
        let deletion := up.down.1[j + 1]'(by rw [up.down.2]; omega) + 1
        let insertion := row.down.1[j]'(by rw [row.down.2]; omega) + 1
        let value := min diagonal (min deletion insertion)
        pure ⟨⟨row.down.1.push value, by simp [row.down.2]⟩⟩
  let Table (m n : Nat) : Type u :=
    ULift.{u} (Subtype (fun data : Array (Array Nat) =>
      data.size = m + 1 ∧ ∀ i (hi : i < data.size), data[i].size = n + 1))
  let cell {m n : Nat} (table : Table m n) (i j : Nat)
      (hi : i ≤ m) (hj : j ≤ n) : Nat :=
    (table.down.1[i]'(by rw [table.down.2.1]; omega))[j]'(by
      rw [table.down.2.2]; omega)
  let rec @[reducible] buildTable (source target : Array α) :
      (i : Nat) → i ≤ source.size → TimeM EditDistanceCost (Table i target.size)
    | 0, _ => do
        let row ← buildInitialRow target.size target.size (by omega)
        pure ⟨⟨#[row.down.1], by simp, by
          intro i hi
          have : i = 0 := by simpa using hi
          subst i
          exact row.down.2⟩⟩
    | i + 1, hi => do
        let table ← buildTable source target i (by omega)
        let up : Row target.size :=
          ⟨⟨table.down.1[i]'(by rw [table.down.2.1]; omega),
            table.down.2.2 i (by rw [table.down.2.1]; omega)⟩⟩
        let row ← buildRow (source[i]'(by omega)) target up (i + 1)
          target.size (by omega)
        pure ⟨⟨table.down.1.push row.down.1, by simp [table.down.2.1], by
          intro k hk
          rw [Array.getElem_push]
          split
          · exact table.down.2.2 _ _
          · exact row.down.2⟩⟩
  let rec @[reducible] reconstruct (source target : Array α)
      (table : Table source.size target.size) :
      (i j : Nat) → i ≤ source.size → j ≤ target.size →
        EditScript α → TimeM EditDistanceCost (EditScript α)
    | 0, 0, _, _, accumulator => pure accumulator
    | 0, j + 1, hi, hj, accumulator => do
        TimeM.tick ⟨0, 1⟩
        reconstruct source target table 0 j hi (by omega)
          (.insert (target[j]'(by omega)) :: accumulator)
    | i + 1, 0, hi, hj, accumulator => do
        TimeM.tick ⟨0, 1⟩
        reconstruct source target table i 0 (by omega) hj
          (.delete (source[i]'(by omega)) :: accumulator)
    | i + 1, j + 1, hi, hj, accumulator => do
        TimeM.tick ⟨0, 1⟩
        let sourceValue := source[i]'(by omega)
        let targetValue := target[j]'(by omega)
        let diagonal := cell table i j (by omega) (by omega) +
          diagonalCost sourceValue targetValue
        let deletion := cell table i (j + 1) (by omega) hj + 1
        let insertion := cell table (i + 1) j hi (by omega) + 1
        if diagonal ≤ deletion ∧ diagonal ≤ insertion then
          reconstruct source target table i j (by omega) (by omega)
            (diagonalStep sourceValue targetValue :: accumulator)
        else if deletion ≤ insertion then
          reconstruct source target table i (j + 1) (by omega) hj
            (.delete sourceValue :: accumulator)
        else
          reconstruct source target table (i + 1) j hi (by omega)
            (.insert targetValue :: accumulator)
  termination_by i j _ _ _ => i + j
  do
    let sourceArray := source.toArray
    let targetArray := target.toArray
    let table ← buildTable sourceArray targetArray sourceArray.size (by omega)
    let script ← reconstruct sourceArray targetArray table sourceArray.size targetArray.size
      (by omega) (by omega) []
    pure {
      distance := cell table sourceArray.size targetArray.size (by omega) (by omega)
      script := script }

end Cslib.Algorithms.Lean

@[expose] public section

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

private def diagonalCost [BEq α] (sourceValue targetValue : α) : Nat :=
  if sourceValue == targetValue then 0 else 1

private def diagonalStep [BEq α] (sourceValue targetValue : α) : EditStep α :=
  if sourceValue == targetValue then .keep sourceValue else .substitute sourceValue targetValue

private abbrev Row (n : Nat) :=
  ULift.{u} (Subtype (fun row : Array Nat => row.size = n + 1))

private abbrev Table (m n : Nat) :=
  ULift.{u} (Subtype (fun data : Array (Array Nat) =>
    data.size = m + 1 ∧ ∀ i (hi : i < data.size), data[i].size = n + 1))

private abbrev cell {m n : Nat} (table : Table m n) (i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) : Nat :=
  (table.down.1[i]'(by rw [table.down.2.1]; omega))[j]'(by
    rw [table.down.2.2]; omega)

private inductive Executes {α : Type u} : EditScript α → List α → List α → Prop
  | nil : Executes [] [] []
  | keep {script : EditScript α} {source target : List α} {value : α}
      (h : Executes script source target) :
      Executes (.keep value :: script) (value :: source) (value :: target)
  | delete {script : EditScript α} {source target : List α} {value : α}
      (h : Executes script source target) :
      Executes (.delete value :: script) (value :: source) target
  | insert {script : EditScript α} {source target : List α} {value : α}
      (h : Executes script source target) :
      Executes (.insert value :: script) source (value :: target)
  | substitute {script : EditScript α} {source target : List α}
      {sourceValue targetValue : α}
      (h : Executes script source target) :
      Executes (.substitute sourceValue targetValue :: script)
        (sourceValue :: source) (targetValue :: target)

private lemma diagonalStep_executes [BEq α] [LawfulBEq α]
    (sourceValue targetValue : α) :
    Executes [diagonalStep sourceValue targetValue] [sourceValue] [targetValue] := by
  simp only [diagonalStep]
  split
  · rename_i heq
    have heq' : sourceValue = targetValue := by simpa using heq
    rw [← heq']
    exact Executes.keep Executes.nil
  · exact Executes.substitute Executes.nil

private lemma diagonalStep_cost [BEq α] (sourceValue targetValue : α) :
    EditScript.cost [diagonalStep sourceValue targetValue] =
      diagonalCost sourceValue targetValue := by
  simp only [diagonalStep, diagonalCost]
  split <;> rfl

private lemma executes_apply {α : Type u} [BEq α] [LawfulBEq α]
    {script : EditScript α} {source target : List α}
    (h : Executes script source target) :
    EditScript.apply? script source = some target := by
  induction h <;> simp_all [EditScript.apply?]

private lemma apply_executes {α : Type u} [BEq α] [LawfulBEq α]
    {script : EditScript α} {source target : List α}
    (h : EditScript.apply? script source = some target) :
    Executes script source target := by
  induction script generalizing source target with
  | nil =>
      cases source <;> simp [EditScript.apply?] at h
      subst target
      exact .nil
  | cons step script ih =>
      cases step <;> cases source <;> simp [EditScript.apply?] at h
      · rename_i value sourceValue source
        obtain ⟨rfl, tail, happly, rfl⟩ := h
        exact .keep (ih happly)
      · rename_i value sourceValue source
        obtain ⟨rfl, h⟩ := h
        exact .delete (ih h)
      · rename_i value
        obtain ⟨tail, happly, rfl⟩ := h
        exact .insert (ih happly)
      · rename_i value sourceValue source
        obtain ⟨tail, happly, rfl⟩ := h
        exact .insert (ih happly)
      · rename_i sourceValue targetValue actual source
        obtain ⟨rfl, tail, happly, rfl⟩ := h
        exact .substitute (ih happly)

private lemma Executes.append
    {firstScript secondScript : EditScript α}
    {firstSource firstTarget secondSource secondTarget : List α}
    (first : Executes firstScript firstSource firstTarget)
    (second : Executes secondScript secondSource secondTarget) :
    Executes (firstScript ++ secondScript) (firstSource ++ secondSource)
      (firstTarget ++ secondTarget) := by
  induction first with
  | nil => simpa using second
  | keep _ ih => simpa using Executes.keep ih
  | delete _ ih => simpa using Executes.delete ih
  | insert _ ih => simpa using Executes.insert ih
  | substitute _ ih => simpa using Executes.substitute ih

private lemma Executes.reverse {script : EditScript α} {source target : List α}
    (h : Executes script source target) :
    Executes script.reverse source.reverse target.reverse := by
  induction h with
  | nil => exact .nil
  | keep h ih => simpa using ih.append (Executes.keep Executes.nil)
  | delete h ih => simpa using ih.append (Executes.delete Executes.nil)
  | insert h ih => simpa using ih.append (Executes.insert Executes.nil)
  | substitute h ih => simpa using ih.append (Executes.substitute Executes.nil)

private lemma scriptCost_append (first second : EditScript α) :
    EditScript.cost (first ++ second) = EditScript.cost first + EditScript.cost second := by
  induction first with
  | nil => simp [EditScript.cost]
  | cons step first ih => simp [EditScript.cost, ih, Nat.add_assoc]

private lemma scriptCost_reverse (script : EditScript α) :
    EditScript.cost script.reverse = EditScript.cost script := by
  induction script with
  | nil => rfl
  | cons step script ih =>
      rw [List.reverse_cons, scriptCost_append, ih]
      cases step <;> simp [EditScript.cost, Nat.add_comm]

private lemma referenceDistance_le_cost {α : Type u} [BEq α] [LawfulBEq α]
    {script : EditScript α} {source target : List α}
    (h : Executes script source target) :
    referenceDistance source target ≤ EditScript.cost script := by
  induction h with
  | nil => simp [referenceDistance, EditScript.cost]
  | @keep script source target value h ih =>
      have hcandidate : referenceDistance (value :: source) (value :: target) ≤
          referenceDistance source target := by
        simp only [referenceDistance, beq_self_eq_true, ite_true, Nat.add_zero]
        exact Nat.min_le_left _ _
      simpa [EditScript.cost, EditStep.cost, Nat.add_comm] using Nat.le_trans hcandidate ih
  | @delete script source target value h ih =>
      have hcandidate : referenceDistance (value :: source) target ≤
          referenceDistance source target + 1 := by
        cases target with
        | nil => cases source <;> simp [referenceDistance]
        | cons targetValue target =>
            simp only [referenceDistance]
            have houter := Nat.min_le_right
              (referenceDistance source target + if value == targetValue then 0 else 1)
              (min (referenceDistance source (targetValue :: target) + 1)
                (referenceDistance (value :: source) target + 1))
            have hinner := Nat.min_le_left
              (referenceDistance source (targetValue :: target) + 1)
              (referenceDistance (value :: source) target + 1)
            omega
      have hbound := Nat.le_trans hcandidate (Nat.add_le_add_right ih 1)
      simpa [EditScript.cost, EditStep.cost, Nat.add_comm] using hbound
  | @insert script source target value h ih =>
      have hcandidate : referenceDistance source (value :: target) ≤
          referenceDistance source target + 1 := by
        cases source with
        | nil => simp [referenceDistance]
        | cons sourceValue source =>
            simp only [referenceDistance]
            have houter := Nat.min_le_right
              (referenceDistance source target + if sourceValue == value then 0 else 1)
              (min (referenceDistance source (value :: target) + 1)
                (referenceDistance (sourceValue :: source) target + 1))
            have hinner := Nat.min_le_right
              (referenceDistance source (value :: target) + 1)
              (referenceDistance (sourceValue :: source) target + 1)
            omega
      have hbound := Nat.le_trans hcandidate (Nat.add_le_add_right ih 1)
      simpa [EditScript.cost, EditStep.cost, Nat.add_comm] using hbound
  | @substitute script source target sourceValue targetValue h ih =>
      have hcandidate :
          referenceDistance (sourceValue :: source) (targetValue :: target) ≤
            referenceDistance source target + 1 := by
        simp only [referenceDistance]
        have hdiagonal := Nat.min_le_left
          (referenceDistance source target + if sourceValue == targetValue then 0 else 1)
          (min (referenceDistance source (targetValue :: target) + 1)
            (referenceDistance (sourceValue :: source) target + 1))
        split <;> omega
      have hbound := Nat.le_trans hcandidate (Nat.add_le_add_right ih 1)
      simpa [EditScript.cost, EditStep.cost, Nat.add_comm] using hbound

private lemma buildInitialRow_correct (n j : Nat) (hj : j ≤ n) :
    ∀ k (hk : k ≤ j),
      (editDistance.buildInitialRow n j hj).ret.down.1[k]'(by
        rw [(editDistance.buildInitialRow n j hj).ret.down.2]; omega) = k := by
  induction j with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      simp [editDistance.buildInitialRow]
  | succ j ih =>
      intro k hk
      simp only [editDistance.buildInitialRow, TimeM.ret_bind, TimeM.ret_pure]
      rw [Array.getElem_push]
      split
      · exact ih (by omega) k (by
          have hs := (editDistance.buildInitialRow n j (by omega)).ret.down.2
          omega)
      · have hs := (editDistance.buildInitialRow n j (by omega)).ret.down.2
        omega

private lemma buildRow_correct {α : Type u} [BEq α] (sourcePrefix : List α)
    (sourceValue : α) (target : Array α) (up : Row target.size)
    (hu : ∀ k (hk : k ≤ target.size),
      up.down.1[k]'(by rw [up.down.2]; omega) =
        referenceDistance sourcePrefix.reverse (target.toList.take k).reverse)
    (j : Nat) (hj : j ≤ target.size) :
    ∀ k (hk : k ≤ j),
      (editDistance.buildRow sourceValue target up (sourcePrefix.length + 1) j hj).ret.down.1[k]'(by
        rw [(editDistance.buildRow sourceValue target up
          (sourcePrefix.length + 1) j hj).ret.down.2]; omega) =
        referenceDistance (sourcePrefix ++ [sourceValue]).reverse
          (target.toList.take k).reverse := by
  induction j with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      simp [editDistance.buildRow, referenceDistance]
  | succ j ih =>
      intro k hk
      simp only [editDistance.buildRow, TimeM.ret_bind, TimeM.ret_pure]
      rw [Array.getElem_push]
      split
      · exact ih (by omega) k (by
          have hs := (editDistance.buildRow sourceValue target up
            (sourcePrefix.length + 1) j (by omega)).ret.down.2
          omega)
      · rename_i hnot
        have hs := (editDistance.buildRow sourceValue target up
          (sourcePrefix.length + 1) j (by omega)).ret.down.2
        have hkj : k = j + 1 := by omega
        subst k
        have hyj : j < target.toList.length := by
          simpa using (show j < target.size from by omega)
        have huSucc := hu (j + 1) (by omega)
        rw [List.take_succ_eq_append_getElem hyj, Array.getElem_toList] at huSucc
        simp only [List.reverse_append, List.reverse_singleton] at huSucc
        rw [List.take_succ_eq_append_getElem hyj, Array.getElem_toList]
        simp only [List.reverse_append, List.reverse_singleton]
        rw [hu j (by omega), huSucc,
          ih (by omega) j (by omega)]
        simp [referenceDistance]

private lemma buildTable_correct {α : Type u} [BEq α] (source target : Array α)
    (i : Nat) (hi : i ≤ source.size) :
    ∀ p q (hp : p ≤ i) (hq : q ≤ target.size),
      cell (editDistance.buildTable source target i hi).ret p q hp hq =
        referenceDistance (source.toList.take p).reverse
          (target.toList.take q).reverse := by
  induction i with
  | zero =>
      intro p q hp hq
      have : p = 0 := by omega
      subst p
      simpa [editDistance.buildTable, cell, referenceDistance, Nat.min_eq_left hq] using
        buildInitialRow_correct target.size target.size (by omega) q hq
  | succ i ih =>
      intro p q hp hq
      simp only [editDistance.buildTable, TimeM.ret_bind, TimeM.ret_pure, cell]
      simp only [Array.getElem_push]
      split
      · exact ih (by omega) p q (by
          have hs := (editDistance.buildTable source target i (by omega)).ret.down.2.1
          omega) hq
      · rename_i hnot
        have hs := (editDistance.buildTable source target i (by omega)).ret.down.2.1
        have hpi : p = i + 1 := by omega
        subst p
        have hxi : i < source.toList.length := by
          simpa using (show i < source.size from by omega)
        rw [List.take_succ_eq_append_getElem hxi, Array.getElem_toList]
        let up : Row target.size :=
          ⟨⟨(editDistance.buildTable source target i (by omega)).ret.down.1[i]'(by
            rw [(editDistance.buildTable source target i (by omega)).ret.down.2.1]; omega),
            (editDistance.buildTable source target i (by omega)).ret.down.2.2 i (by
              rw [(editDistance.buildTable source target i (by omega)).ret.down.2.1]; omega)⟩⟩
        have hlength : (source.toList.take i).length = i := by
          rw [List.length_take_of_le]
          simpa using (show i ≤ source.size from by omega)
        simpa [hlength] using
          buildRow_correct (source.toList.take i) (source[i]'(by omega)) target up
            (fun k hk => ih (by omega) i k (by omega) hk)
            target.size (by omega) q hq

private lemma cell_zero_left {α : Type u} [BEq α] (source target : Array α)
    (table : Table source.size target.size)
    (ho : ∀ p q (hp : p ≤ source.size) (hq : q ≤ target.size),
      cell table p q hp hq = referenceDistance (source.toList.take p).reverse
        (target.toList.take q).reverse)
    (j : Nat) (hj : j ≤ target.size) :
    cell table 0 j (by omega) hj = j := by
  rw [ho]
  simp [referenceDistance, List.length_take, Nat.min_eq_left hj]

private lemma cell_zero_right {α : Type u} [BEq α] (source target : Array α)
    (table : Table source.size target.size)
    (ho : ∀ p q (hp : p ≤ source.size) (hq : q ≤ target.size),
      cell table p q hp hq = referenceDistance (source.toList.take p).reverse
        (target.toList.take q).reverse)
    (i : Nat) (hi : i ≤ source.size) :
    cell table i 0 hi (by omega) = i := by
  rw [ho]
  simp only [List.take_zero, List.reverse_nil]
  rw [referenceDistance_nil_right]
  simp [List.length_take, Nat.min_eq_left hi]

private lemma cell_recurrence {α : Type u} [BEq α] (source target : Array α)
    (table : Table source.size target.size)
    (ho : ∀ p q (hp : p ≤ source.size) (hq : q ≤ target.size),
      cell table p q hp hq = referenceDistance (source.toList.take p).reverse
        (target.toList.take q).reverse)
    (i j : Nat) (hi : i + 1 ≤ source.size) (hj : j + 1 ≤ target.size) :
    cell table (i + 1) (j + 1) hi hj =
      min (cell table i j (by omega) (by omega) +
        if source[i] == target[j] then 0 else 1)
        (min (cell table i (j + 1) (by omega) hj + 1)
          (cell table (i + 1) j hi (by omega) + 1)) := by
  have hxi : i < source.toList.length := by
    simpa using (show i < source.size from by omega)
  have hyj : j < target.toList.length := by
    simpa using (show j < target.size from by omega)
  rw [ho, ho, ho, ho]
  rw [List.take_succ_eq_append_getElem hxi, List.take_succ_eq_append_getElem hyj,
    Array.getElem_toList, Array.getElem_toList]
  simp [referenceDistance]

private lemma reconstruct_correct {α : Type u} [BEq α] [LawfulBEq α]
    (source target : Array α) (table : Table source.size target.size)
    (ho : ∀ p q (hp : p ≤ source.size) (hq : q ≤ target.size),
      cell table p q hp hq = referenceDistance (source.toList.take p).reverse
        (target.toList.take q).reverse)
    (i j : Nat) (hi : i ≤ source.size) (hj : j ≤ target.size)
    (accumulator : EditScript α) :
    ∃ script,
      (editDistance.reconstruct diagonalCost diagonalStep cell source target table
        i j hi hj accumulator).ret =
        script ++ accumulator ∧
      Executes script (source.toList.take i) (target.toList.take j) ∧
      EditScript.cost script = cell table i j hi hj ∧
      script.length ≤ i + j := by
  fun_induction editDistance.reconstruct with
  | case1 hi hj accumulator =>
      refine ⟨[], by simp, Executes.nil, ?_, by simp⟩
      rw [ho]
      simp [EditScript.cost, referenceDistance]
  | case2 j hi hj accumulator _ _ ih =>
      obtain ⟨script, hret, hexec, hcost, hlength⟩ := ih
      refine ⟨script ++ [.insert target[j]], ?_, ?_, ?_, ?_⟩
      · simpa [List.append_assoc] using hret
      · have hyj : j < target.toList.length := by
          simpa using (show j < target.size from by omega)
        rw [List.take_succ_eq_append_getElem hyj, Array.getElem_toList]
        exact hexec.append (Executes.insert Executes.nil)
      · rw [scriptCost_append, hcost]
        rw [cell_zero_left source target table ho j (by omega),
          cell_zero_left source target table ho (j + 1) hj]
        simp [EditScript.cost, EditStep.cost]
      · simp only [List.length_append, List.length_singleton]
        omega
  | case3 i hi hj accumulator _ _ ih =>
      obtain ⟨script, hret, hexec, hcost, hlength⟩ := ih
      refine ⟨script ++ [.delete source[i]], ?_, ?_, ?_, ?_⟩
      · simpa [List.append_assoc] using hret
      · have hxi : i < source.toList.length := by
          simpa using (show i < source.size from by omega)
        have hstep := hexec.append
          (Executes.delete (value := source[i]) Executes.nil)
        simpa only [List.take_zero, List.append_nil,
          List.take_succ_eq_append_getElem hxi, Array.getElem_toList] using hstep
      · rw [scriptCost_append, hcost]
        rw [cell_zero_right source target table ho i (by omega),
          cell_zero_right source target table ho (i + 1) hi]
        simp [EditScript.cost, EditStep.cost]
      · simp only [List.length_append, List.length_singleton]
        omega
  | case4 i j hi hj accumulator _ _ ihDiagonal ihDelete ihInsert =>
      simp only [editDistance.reconstruct, TimeM.ret_bind]
      let sourceValue := source[i]'(by omega)
      let targetValue := target[j]'(by omega)
      let diagonal := cell table i j (by omega) (by omega) +
        diagonalCost sourceValue targetValue
      let deletion := cell table i (j + 1) (by omega) hj + 1
      let insertion := cell table (i + 1) j hi (by omega) + 1
      have hrecurrence := cell_recurrence source target table ho i j hi hj
      split
      · rename_i hchoose
        obtain ⟨script, hret, hexec, hcost, hlength⟩ := ihDiagonal
        refine ⟨script ++ [diagonalStep sourceValue targetValue],
          ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc, sourceValue, targetValue] using hret
        · have hxi : i < source.toList.length := by
            simpa using (show i < source.size from by omega)
          have hyj : j < target.toList.length := by
            simpa using (show j < target.size from by omega)
          rw [List.take_succ_eq_append_getElem hxi,
            List.take_succ_eq_append_getElem hyj, Array.getElem_toList,
            Array.getElem_toList]
          exact hexec.append (diagonalStep_executes sourceValue targetValue)
        · rw [scriptCost_append, hcost]
          have hcurrent : cell table (i + 1) (j + 1) hi hj = diagonal := by
            rw [hrecurrence]
            simp only [diagonal, diagonalCost,
              sourceValue, targetValue] at hchoose ⊢
            omega
          rw [hcurrent]
          rw [diagonalStep_cost]
        · simp only [List.length_append, List.length_singleton]
          omega
      · rename_i hnotDiagonal
        split
        · rename_i hchooseDelete
          obtain ⟨script, hret, hexec, hcost, hlength⟩ := ihDelete
          refine ⟨script ++ [.delete sourceValue], ?_, ?_, ?_, ?_⟩
          · simpa [List.append_assoc, sourceValue] using hret
          · have hxi : i < source.toList.length := by
              simpa using (show i < source.size from by omega)
            have hstep := hexec.append
              (Executes.delete (value := sourceValue) Executes.nil)
            simpa only [sourceValue, Nat.add_one, List.append_nil,
              List.take_succ_eq_append_getElem hxi, Array.getElem_toList] using hstep
          · rw [scriptCost_append, hcost]
            have hcurrent : cell table (i + 1) (j + 1) hi hj = deletion := by
              rw [hrecurrence]
              simp only [deletion, diagonalCost] at hnotDiagonal hchooseDelete ⊢
              omega
            rw [hcurrent]
            simp [EditScript.cost, EditStep.cost, deletion]
          · simp only [List.length_append, List.length_singleton]
            omega
        · rename_i hnotDelete
          obtain ⟨script, hret, hexec, hcost, hlength⟩ := ihInsert
          refine ⟨script ++ [.insert targetValue], ?_, ?_, ?_, ?_⟩
          · simpa [List.append_assoc, targetValue] using hret
          · have hyj : j < target.toList.length := by
              simpa using (show j < target.size from by omega)
            have hstep := hexec.append
              (Executes.insert (value := targetValue) Executes.nil)
            simpa only [targetValue, Nat.add_one, List.append_nil,
              List.take_succ_eq_append_getElem hyj, Array.getElem_toList] using hstep
          · rw [scriptCost_append, hcost]
            have hcurrent : cell table (i + 1) (j + 1) hi hj = insertion := by
              rw [hrecurrence]
              simp only [insertion, diagonalCost] at hnotDiagonal hnotDelete ⊢
              omega
            rw [hcurrent]
            simp [EditScript.cost, EditStep.cost, insertion]
          · simp only [List.length_append, List.length_singleton]
            omega

private lemma reconstruct_metrics {α : Type u} [BEq α]
    (source target : Array α) (table : Table source.size target.size)
    (ho : ∀ p q (hp : p ≤ source.size) (hq : q ≤ target.size),
      cell table p q hp hq = referenceDistance (source.toList.take p).reverse
        (target.toList.take q).reverse)
    (i j : Nat) (hi : i ≤ source.size) (hj : j ≤ target.size)
    (accumulator : EditScript α) :
    ∃ script,
      (editDistance.reconstruct diagonalCost diagonalStep cell source target table
        i j hi hj accumulator).ret = script ++ accumulator ∧
      EditScript.cost script = cell table i j hi hj ∧
      script.length ≤ i + j ∧
      (editDistance.reconstruct diagonalCost diagonalStep cell source target table
        i j hi hj accumulator).time = ⟨0, script.length⟩ := by
  fun_induction editDistance.reconstruct with
  | case1 hi hj accumulator =>
      refine ⟨[], by simp, ?_, by simp, by rfl⟩
      rw [ho]
      simp [EditScript.cost, referenceDistance]
  | case2 j hi hj accumulator _ _ ih =>
      obtain ⟨script, hret, hcost, hlength, htime⟩ := ih
      refine ⟨script ++ [.insert target[j]], ?_, ?_, ?_, ?_⟩
      · simpa [List.append_assoc] using hret
      · rw [scriptCost_append, hcost]
        rw [cell_zero_left source target table ho j (by omega),
          cell_zero_left source target table ho (j + 1) hj]
        simp [EditScript.cost, EditStep.cost]
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [editDistance.reconstruct, TimeM.time_bind, TimeM.time_tick, htime,
          List.length_append, List.length_singleton]
        change EditDistanceCost.mk (0 + 0) (1 + script.length) =
          EditDistanceCost.mk 0 (script.length + 1)
        congr 1 <;> omega
  | case3 i hi hj accumulator _ _ ih =>
      obtain ⟨script, hret, hcost, hlength, htime⟩ := ih
      refine ⟨script ++ [.delete source[i]], ?_, ?_, ?_, ?_⟩
      · simpa [List.append_assoc] using hret
      · rw [scriptCost_append, hcost]
        rw [cell_zero_right source target table ho i (by omega),
          cell_zero_right source target table ho (i + 1) hi]
        simp [EditScript.cost, EditStep.cost]
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [editDistance.reconstruct, TimeM.time_bind, TimeM.time_tick, htime,
          List.length_append, List.length_singleton]
        change EditDistanceCost.mk (0 + 0) (1 + script.length) =
          EditDistanceCost.mk 0 (script.length + 1)
        congr 1 <;> omega
  | case4 i j hi hj accumulator _ _ ihDiagonal ihDelete ihInsert =>
      simp only [editDistance.reconstruct, TimeM.ret_bind]
      let sourceValue := source[i]'(by omega)
      let targetValue := target[j]'(by omega)
      let diagonal := cell table i j (by omega) (by omega) +
        diagonalCost sourceValue targetValue
      let deletion := cell table i (j + 1) (by omega) hj + 1
      let insertion := cell table (i + 1) j hi (by omega) + 1
      have hrecurrence := cell_recurrence source target table ho i j hi hj
      split
      · rename_i hchoose
        obtain ⟨script, hret, hcost, hlength, htime⟩ := ihDiagonal
        refine ⟨script ++ [diagonalStep sourceValue targetValue], ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc, sourceValue, targetValue] using hret
        · rw [scriptCost_append, hcost]
          have hcurrent : cell table (i + 1) (j + 1) hi hj = diagonal := by
            rw [hrecurrence]
            simp only [diagonal, diagonalCost,
              sourceValue, targetValue] at hchoose ⊢
            omega
          rw [hcurrent, diagonalStep_cost]
        · simp only [List.length_append, List.length_singleton]
          omega
        · simp only [TimeM.time_bind, TimeM.time_tick, htime,
            List.length_append, List.length_singleton]
          change EditDistanceCost.mk (0 + 0) (1 + script.length) =
            EditDistanceCost.mk 0 (script.length + 1)
          congr 1 <;> omega
      · rename_i hnotDiagonal
        split
        · rename_i hchooseDelete
          obtain ⟨script, hret, hcost, hlength, htime⟩ := ihDelete
          refine ⟨script ++ [.delete sourceValue], ?_, ?_, ?_, ?_⟩
          · simpa [List.append_assoc, sourceValue] using hret
          · rw [scriptCost_append, hcost]
            have hcurrent : cell table (i + 1) (j + 1) hi hj = deletion := by
              rw [hrecurrence]
              simp only [deletion, diagonalCost] at hnotDiagonal hchooseDelete ⊢
              omega
            rw [hcurrent]
            simp [EditScript.cost, EditStep.cost, deletion]
          · simp only [List.length_append, List.length_singleton]
            omega
          · simp only [TimeM.time_bind, TimeM.time_tick, htime,
              List.length_append, List.length_singleton]
            change EditDistanceCost.mk (0 + 0) (1 + script.length) =
              EditDistanceCost.mk 0 (script.length + 1)
            congr 1 <;> omega
        · rename_i hnotDelete
          obtain ⟨script, hret, hcost, hlength, htime⟩ := ihInsert
          refine ⟨script ++ [.insert targetValue], ?_, ?_, ?_, ?_⟩
          · simpa [List.append_assoc, targetValue] using hret
          · rw [scriptCost_append, hcost]
            have hcurrent : cell table (i + 1) (j + 1) hi hj = insertion := by
              rw [hrecurrence]
              simp only [insertion, diagonalCost] at hnotDiagonal hnotDelete ⊢
              omega
            rw [hcurrent]
            simp [EditScript.cost, EditStep.cost, insertion]
          · simp only [List.length_append, List.length_singleton]
            omega
          · simp only [TimeM.time_bind, TimeM.time_tick, htime,
              List.length_append, List.length_singleton]
            change EditDistanceCost.mk (0 + 0) (1 + script.length) =
              EditDistanceCost.mk 0 (script.length + 1)
            congr 1 <;> omega

private lemma editDistance_value [BEq α] (source target : List α) :
    (editDistance source target).ret.distance =
      referenceDistance source.reverse target.reverse := by
  simp only [editDistance, TimeM.ret_bind, TimeM.ret_pure]
  simpa using buildTable_correct source.toArray target.toArray source.toArray.size (by omega)
    source.toArray.size target.toArray.size (by omega) (by omega)

private lemma editDistance_script_facts [BEq α] [LawfulBEq α]
    (source target : List α) :
    Executes (editDistance source target).ret.script source target ∧
      (editDistance source target).ret.script.cost =
        (editDistance source target).ret.distance ∧
      (editDistance source target).ret.script.length ≤ source.length + target.length := by
  simp only [editDistance, TimeM.ret_bind, TimeM.ret_pure]
  let table := (editDistance.buildTable source.toArray target.toArray
    source.toArray.size (by omega)).ret
  have ho := buildTable_correct source.toArray target.toArray source.toArray.size (by omega)
  obtain ⟨script, hret, hexec, hcost, hlength⟩ := reconstruct_correct
    source.toArray target.toArray table ho source.toArray.size target.toArray.size
    (by omega) (by omega) []
  change Executes
      (editDistance.reconstruct diagonalCost diagonalStep cell source.toArray target.toArray table
        source.toArray.size target.toArray.size (by omega) (by omega) []).ret source target ∧
    (editDistance.reconstruct diagonalCost diagonalStep cell source.toArray target.toArray table
          source.toArray.size target.toArray.size (by omega) (by omega) []).ret.cost =
      cell table source.toArray.size target.toArray.size (by omega) (by omega) ∧
    (editDistance.reconstruct diagonalCost diagonalStep cell source.toArray target.toArray table
          source.toArray.size target.toArray.size (by omega) (by omega) []).ret.length ≤
      source.length + target.length
  rw [hret]
  simpa [table] using And.intro hexec (And.intro hcost hlength)

private lemma editDistance_script_metrics [BEq α] (source target : List α) :
    (editDistance source target).ret.script.cost =
        (editDistance source target).ret.distance ∧
      (editDistance source target).ret.script.length ≤ source.length + target.length ∧
      let sourceArray := source.toArray
      let targetArray := target.toArray
      let table := (editDistance.buildTable sourceArray targetArray sourceArray.size (by omega)).ret
      (editDistance.reconstruct diagonalCost diagonalStep cell sourceArray targetArray table
        sourceArray.size targetArray.size (by omega) (by omega) []).time =
        ⟨0, (editDistance source target).ret.script.length⟩ := by
  simp only [editDistance, TimeM.ret_bind, TimeM.ret_pure]
  let table := (editDistance.buildTable source.toArray target.toArray
    source.toArray.size (by omega)).ret
  have ho := buildTable_correct source.toArray target.toArray source.toArray.size (by omega)
  obtain ⟨script, hret, hcost, hlength, htime⟩ := reconstruct_metrics
    source.toArray target.toArray table ho source.toArray.size target.toArray.size
    (by omega) (by omega) []
  change (editDistance.reconstruct diagonalCost diagonalStep cell source.toArray target.toArray table
          source.toArray.size target.toArray.size (by omega) (by omega) []).ret.cost =
      cell table source.toArray.size target.toArray.size (by omega) (by omega) ∧
    (editDistance.reconstruct diagonalCost diagonalStep cell source.toArray target.toArray table
          source.toArray.size target.toArray.size (by omega) (by omega) []).ret.length ≤
      source.length + target.length ∧
    (editDistance.reconstruct diagonalCost diagonalStep cell source.toArray target.toArray table
          source.toArray.size target.toArray.size (by omega) (by omega) []).time =
      ⟨0, (editDistance.reconstruct diagonalCost diagonalStep cell source.toArray target.toArray table
        source.toArray.size target.toArray.size (by omega) (by omega) []).ret.length⟩
  rw [hret]
  simpa [table] using And.intro hcost (And.intro hlength htime)

private lemma buildInitialRow_time (n j : Nat) (hj : j ≤ n) :
    (editDistance.buildInitialRow n j hj).time = ⟨j + 1, 0⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [editDistance.buildInitialRow, TimeM.time_bind, TimeM.time_tick,
        TimeM.time_pure, ih (by omega)]
      change EditDistanceCost.mk ((j + 1) + 1 + 0) (0 + 0 + 0) =
        EditDistanceCost.mk (j + 1 + 1) 0
      rfl

private lemma buildRow_time [BEq α] (sourceValue : α) (target : Array α)
    (up : Row target.size) (first j : Nat) (hj : j ≤ target.size) :
    (editDistance.buildRow sourceValue target up first j hj).time = ⟨j + 1, 0⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [editDistance.buildRow, TimeM.time_bind, TimeM.time_tick,
        TimeM.time_pure, ih (by omega)]
      change EditDistanceCost.mk ((j + 1) + 1 + 0) (0 + 0 + 0) =
        EditDistanceCost.mk (j + 1 + 1) 0
      rfl

private lemma buildTable_time [BEq α] (source target : Array α)
    (i : Nat) (hi : i ≤ source.size) :
    (editDistance.buildTable source target i hi).time =
      ⟨(i + 1) * (target.size + 1), 0⟩ := by
  induction i with
  | zero =>
      simp only [editDistance.buildTable, TimeM.time_bind, TimeM.time_pure,
        buildInitialRow_time]
      change EditDistanceCost.mk (target.size + 1 + 0) (0 + 0) =
        EditDistanceCost.mk ((0 + 1) * (target.size + 1)) 0
      simp
  | succ i ih =>
      simp only [editDistance.buildTable, TimeM.time_bind, TimeM.time_pure,
        ih (by omega), buildRow_time]
      change EditDistanceCost.mk
        ((i + 1) * (target.size + 1) + (target.size + 1) + 0) (0 + 0 + 0) =
        EditDistanceCost.mk ((i + 1 + 1) * (target.size + 1)) 0
      congr 1
      simp [Nat.add_mul, Nat.add_assoc]
      omega

private lemma editDistance_time_spec [BEq α] (source target : List α) :
    (editDistance source target).time =
      ⟨(source.length + 1) * (target.length + 1),
        (editDistance source target).ret.script.length⟩ := by
  set resultLength := (editDistance source target).ret.script.length with hresultLength
  change (editDistance source target).time =
    ⟨(source.length + 1) * (target.length + 1), resultLength⟩
  simp only [editDistance, TimeM.time_bind, TimeM.time_pure]
  let table := (editDistance.buildTable source.toArray target.toArray
    source.toArray.size (by omega)).ret
  have htable := buildTable_time source.toArray target.toArray source.toArray.size (by omega)
  have hreconstruct := (editDistance_script_metrics source target).2.2
  rw [← hresultLength] at hreconstruct
  change (editDistance.buildTable source.toArray target.toArray source.toArray.size
      (by omega)).time +
      (editDistance.reconstruct diagonalCost diagonalStep cell source.toArray target.toArray table
        source.toArray.size target.toArray.size (by omega) (by omega) []).time + 0 = _
  rw [htable]
  change EditDistanceCost.mk ((source.length + 1) * (target.length + 1)) 0 +
      (editDistance.reconstruct diagonalCost diagonalStep cell source.toArray target.toArray table
        source.toArray.size target.toArray.size (by omega) (by omega) []).time + 0 = _
  rw [hreconstruct]
  change EditDistanceCost.mk
      ((source.length + 1) * (target.length + 1) + 0 + 0)
      (0 + resultLength + 0) = _
  congr 1 <;> omega

private lemma referenceDistance_self [BEq α] [LawfulBEq α] (source : List α) :
    referenceDistance source source = 0 := by
  induction source with
  | nil => simp [referenceDistance]
  | cons value source ih => simp [referenceDistance, ih]

private lemma Executes.eq_of_cost_zero {script : EditScript α} {source target : List α}
    (h : Executes script source target)
    (hcost : EditScript.cost script = 0) : source = target := by
  induction h with
  | nil => rfl
  | @keep script source target value h ih =>
      have htail : EditScript.cost script = 0 := by
        simpa [EditScript.cost, EditStep.cost] using hcost
      simpa using congrArg (value :: ·) (ih htail)
  | delete h ih => simp [EditScript.cost, EditStep.cost] at hcost
  | insert h ih => simp [EditScript.cost, EditStep.cost] at hcost
  | substitute h ih => simp [EditScript.cost, EditStep.cost] at hcost

/-- The returned script executes on the source and produces the target. -/
theorem editDistance_script_applies [BEq α] [LawfulBEq α] (source target : List α) :
    (editDistance source target).ret.script.Transforms source target := by
  exact executes_apply (editDistance_script_facts source target).1

/-- The returned script's unit cost is the reported distance. -/
theorem editDistance_script_cost [BEq α] (source target : List α) :
    (editDistance source target).ret.script.cost =
      (editDistance source target).ret.distance :=
  (editDistance_script_metrics source target).1

/-- No valid edit script costs less than the reported distance. -/
theorem editDistance_minimal [BEq α] [LawfulBEq α]
    (source target : List α) (script : EditScript α) :
    script.Transforms source target →
      (editDistance source target).ret.distance ≤ script.cost := by
  intro htransforms
  have hexec := (apply_executes htransforms).reverse
  have hbound := referenceDistance_le_cost hexec
  rw [scriptCost_reverse] at hbound
  simpa [editDistance_value source target] using hbound

/-- Distance from the empty list is the target length. -/
theorem editDistance_nil_left [BEq α] (target : List α) :
    (editDistance [] target).ret.distance = target.length := by
  rw [editDistance_value]
  simp [referenceDistance]

/-- Distance to the empty list is the source length. -/
theorem editDistance_nil_right [BEq α] (source : List α) :
    (editDistance source []).ret.distance = source.length := by
  rw [editDistance_value]
  simp only [List.reverse_nil]
  rw [referenceDistance_nil_right, List.length_reverse]

/-- Every list has distance zero from itself. -/
theorem editDistance_self [BEq α] [LawfulBEq α] (source : List α) :
    (editDistance source source).ret.distance = 0 := by
  rw [editDistance_value]
  exact referenceDistance_self source.reverse

/-- Unit-cost edit distance is zero exactly for equal lists. -/
theorem editDistance_eq_zero_iff [BEq α] [LawfulBEq α] (source target : List α) :
    (editDistance source target).ret.distance = 0 ↔ source = target := by
  constructor
  · intro hzero
    exact (editDistance_script_facts source target).1.eq_of_cost_zero
      ((editDistance_script_cost source target).trans hzero)
  · rintro rfl
    exact editDistance_self source

/-- The table recursion charges exactly one transition per prefix pair. -/
theorem editDistance_cellTransitions [BEq α] (source target : List α) :
    (editDistance source target).time.cellTransitions =
      (source.length + 1) * (target.length + 1) := by
  exact congrArg EditDistanceCost.cellTransitions (editDistance_time_spec source target)

/-- Reconstruction charges exactly one step per emitted operation. -/
theorem editDistance_reconstructionSteps [BEq α] (source target : List α) :
    (editDistance source target).time.reconstructionSteps =
      (editDistance source target).ret.script.length := by
  exact congrArg EditDistanceCost.reconstructionSteps (editDistance_time_spec source target)

/-- Reconstruction emits at most one operation per consumed or produced symbol. -/
theorem editDistance_reconstructionSteps_le [BEq α] (source target : List α) :
    (editDistance source target).time.reconstructionSteps ≤ source.length + target.length := by
  rw [editDistance_reconstructionSteps]
  exact (editDistance_script_metrics source target).2.1

/-- Total charged events are all table cells plus all reconstructed operations. -/
theorem editDistance_time [BEq α] (source target : List α) :
    (editDistance source target).time.total =
      (source.length + 1) * (target.length + 1) +
        (editDistance source target).ret.script.length := by
  simp only [EditDistanceCost.total, editDistance_cellTransitions,
    editDistance_reconstructionSteps]
end Cslib.Algorithms.Lean
