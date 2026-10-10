/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import all CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Internal.Construction

/-!
# Private optimal-BST interval-table invariant

Source: CLRS, fourth edition, Section 14.5, pages 400-407 and Figure 14.10.
The induction follows the actual ascending interval starts and lengths. Previously
saved shorter intervals justify each executed candidate and all meaningful saved
cost, weight, and root cells, including the empty intervals.
-/

set_option autoImplicit false
universe u
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BinarySearchTree
open scoped BigOperators
namespace Cslib.Algorithms.Lean.OptimalBST
variable {R : Type u}

universe v w

private theorem fold_order_invariant {α : Type v} {β : Type w}
    (value : α → Nat) (step : β → α → β) (P : Nat → β → Prop)
    (hStep : ∀ state item, P (value item) state →
      P (value item + 1) (step state item))
    (items : List α) (start : Nat)
    (hOrder : items.map value = List.range' start items.length)
    (initial : β) (hInitial : P start initial) :
    P (start + items.length) (items.foldl step initial) := by
  induction items generalizing start initial with
  | nil => simpa using hInitial
  | cons item rest ih =>
    have hValue : value item = start := by
      have h := congrArg List.head? hOrder
      simpa [List.head?_range'] using h
    have hRest : rest.map value = List.range' (start + 1) rest.length := by
      have h := congrArg List.tail hOrder
      simpa using h
    have hNext : P (start + 1) (step initial item) := by
      simpa only [hValue] using hStep initial item (by simpa only [hValue] using hInitial)
    simpa only [List.length_cons, List.foldl_cons, Nat.add_assoc,
      Nat.add_comm 1] using ih (start + 1) hRest (step initial item) hNext

private theorem settled_write [AddCommMonoid R] [LinearOrder R]
    {n : Nat} (p : Vector R n) (q : Vector R (n + 1))
    (e w : Vector (Vector R (n + 1)) (n + 1))
    (root : Vector (Vector (Option (Fin n)) n) n)
    (a length : Nat) (hLength : 0 < length) (hEnd : a + length ≤ n)
    (hSettled : Settled p q e w root length a) :
    let b := a + length
    let savedWeight := w[a][b - 1] + p[b - 1] + q[b]
    let cost (r : Fin n) :=
      e[a][r.val] + e[r.val + 1][b] + savedWeight
    let firstRoot : Fin n := ⟨a, by omega⟩
    let chosen := scanPrefix cost firstRoot (length - 1)
      (by dsimp [firstRoot]; omega)
    Settled p q
      (e.set a (e[a].set b (cost chosen)))
      (w.set a (w[a].set b savedWeight))
      (root.set a (root[a].set (b - 1) (some chosen)))
      length (a + 1) := by
  dsimp only
  let b := a + length
  let savedWeight := w[a][b - 1] + p[b - 1] + q[b]
  let cost (r : Fin n) :=
    e[a][r.val] + e[r.val + 1][b] + savedWeight
  let firstRoot : Fin n := ⟨a, by omega⟩
  let chosen := scanPrefix cost firstRoot (length - 1)
    (by dsimp [firstRoot]; omega)
  let aFin : Fin n := ⟨a, by omega⟩
  let bFin : Fin (n + 1) := ⟨b, by omega⟩
  have hOldWeight :
      w[a][b - 1] = intervalMass p q a (b - 1) := by
    exact hSettled.2.1 aFin.castSucc
      (⟨b - 1, by omega⟩ : Fin (n + 1))
      (by dsimp [aFin, b]; omega)
      (Or.inl (by dsimp [aFin, b]; omega))
  have hWeight : savedWeight = intervalMass p q a b := by
    dsimp [savedWeight]
    rw [hOldWeight]
    exact (intervalMass_step p q a b (by dsimp [b]; omega)
      (by dsimp [b]; omega)).symm
  have hCurrent :
      CellSpec p q
        (e.set a (e[a].set b (cost chosen)))
        (root.set a (root[a].set (b - 1) (some chosen)))
        aFin bFin (by dsimp [aFin, bFin, b]; omega) := by
    simpa [cost, chosen, firstRoot, aFin, bFin, b, hWeight] using
      (cell_selected_spec p q e root aFin bFin
        (by dsimp [aFin, bFin, b]; omega))
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (cell_frame_shorter e aFin.castSucc bFin i i (cost chosen)
      (by dsimp [aFin, bFin, b]; omega)).trans (hSettled.1 i)
  · intro i j hij hProcessed
    by_cases hCell : i.val = a ∧ j.val = b
    · rcases hCell with ⟨hi, hj⟩
      have hi' : i = aFin.castSucc := Fin.ext hi
      have hj' : j = bFin := Fin.ext hj
      subst i
      subst j
      simpa [aFin, bFin, b] using hWeight
    · have hOld :
          j.val - i.val < length ∨
            j.val - i.val = length ∧ i.val < a := by
        rcases hProcessed with hShort | ⟨hWidth, hStart⟩
        · exact Or.inl hShort
        · refine Or.inr ⟨hWidth, ?_⟩
          by_contra hNot
          have hi : i.val = a := by omega
          have hj : j.val = b := by dsimp [b]; omega
          exact hCell ⟨hi, hj⟩
      have hFrame :
          (w.set a (w[a].set b savedWeight))[i.val][j.val] =
            w[i.val][j.val] := by
        rcases hOld with hShort | hEarlier
        · exact cell_frame_shorter w aFin.castSucc bFin i j savedWeight
            (by simpa [aFin, bFin, b] using hShort)
        · exact cell_frame_other_start w aFin.castSucc bFin i j savedWeight
            (by
              intro hi
              have hiVal := congrArg Fin.val hi
              dsimp [aFin] at hiVal
              omega)
      rw [hFrame]
      exact hSettled.2.1 i j hij hOld
  · intro i j hij hProcessed
    by_cases hCell : i.val = a ∧ j.val = b
    · rcases hCell with ⟨hi, hj⟩
      have hi' : i = aFin := Fin.ext hi
      have hj' : j = bFin := Fin.ext hj
      subst i
      subst j
      exact hCurrent
    · have hOld :
          j.val - i.val < length ∨
            j.val - i.val = length ∧ i.val < a := by
        rcases hProcessed with hShort | ⟨hWidth, hStart⟩
        · exact Or.inl hShort
        · refine Or.inr ⟨hWidth, ?_⟩
          by_contra hNot
          have hi : i.val = a := by omega
          have hj : j.val = b := by dsimp [b]; omega
          exact hCell ⟨hi, hj⟩
      have hPrior :
          j.val - i.val < bFin.val - aFin.val ∨ i ≠ aFin := by
        rcases hOld with hShort | hEarlier
        · exact Or.inl (by simpa [aFin, bFin, b] using hShort)
        · exact Or.inr (by
            intro hi
            have hiVal := congrArg Fin.val hi
            dsimp [aFin] at hiVal
            omega)
      exact cellSpec_prior p q e root aFin i bFin j
        (by dsimp [aFin, bFin, b]; omega) hij (cost chosen) chosen
        (by
          rcases hProcessed with hShort | hSame
          · dsimp [aFin, bFin, b]
            omega
          · dsimp [aFin, bFin, b]
            omega)
        hPrior (hSettled.2.2 i j hij hOld)

private theorem starts_prefix [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1))
    (e₀ w₀ : Vector (Vector R (n + 1)) (n + 1))
    (roots₀ : Vector (Vector (Option (Fin n)) n) n)
    (savedCount length m : Nat) (hLength : 0 < length)
    (hLengthN : length ≤ n) (hm : m ≤ n - length + 1)
    (hSettled : Settled p q e₀ w₀ roots₀ length 0) :
    let result : Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector (Option (Fin n)) n) n × Nat := Id.run do
      let mut e := e₀
      let mut w := w₀
      let mut root := roots₀
      let mut candidateCount := savedCount
      for ha : a in [:m] do
        have hStart : a < n - length + 1 := by
          have h : a < m := ha.2.1
          omega
        let b := a + length
        have hB : b ≤ n := by omega
        have hA : a < n := by omega
        let savedWeight := w[a][b - 1] + p[b - 1] + q[b]
        w := w.set a (w[a].set b savedWeight)
        let firstRoot : Fin n := ⟨a, hA⟩
        let firstCandidate := e[a][a] + e[a + 1][b] + savedWeight
        let initialBest : WithTop R :=
          if (firstCandidate : WithTop R) < ⊤ then firstCandidate else ⊤
        have finiteInitial : initialBest ≠ ⊤ := by
          simp [initialBest]
        let mut best := initialBest.untop finiteInitial
        let mut chosen := firstRoot
        candidateCount := candidateCount + 1
        for hr : rootOffset in [:length - 1] do
          have hRootOffset : rootOffset < length - 1 := hr.2.1
          let rootIndex := a + rootOffset + 1
          have hRoot : rootIndex < n := by omega
          have hLeft : rootIndex < n + 1 := by omega
          have hRight : rootIndex + 1 < n + 1 := by omega
          let candidate := e[a][rootIndex] + e[rootIndex + 1][b] + savedWeight
          if candidate < best then
            best := candidate
            chosen := ⟨rootIndex, hRoot⟩
          candidateCount := candidateCount + 1
        e := e.set a (e[a].set b best)
        root := root.set a (root[a].set (b - 1) (some chosen))
      return (e, w, root, candidateCount)
    Settled p q result.1 result.2.1 result.2.2.1 length m := by
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, yield_if,
    List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  convert (fold_order_invariant
    (fun item : {a : Nat // a ∈ List.range' 0 m} => item.val) _
    (fun a (state : Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector (Option (Fin n)) n) n × Nat) =>
        Settled p q state.1 state.2.1 state.2.2.1 length a)
    ?_ (List.range' 0 m).attach 0 (by simp)
    (e₀, w₀, roots₀, savedCount) hSettled) using 1
  · simp
  · intro state item hState
    have hItem := List.mem_range'.mp item.property
    have hWrite := interval_write p q state.1 state.2.1 state.2.2.1
      item.val length hLength (by omega) state.2.2.2
    have hPreserved := settled_write p q state.1 state.2.1 state.2.2.1
      item.val length hLength (by omega) hState
    dsimp only at hWrite hPreserved
    have hLift := congrArg (fun (saved : Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector (Option (Fin n)) n) n × Nat) =>
        Settled p q saved.1 saved.2.1 saved.2.2.1 length (item.val + 1)) hWrite
    have hActual := hLift.mpr hPreserved
    simpa only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, yield_if,
      List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure] using hActual

private theorem lengths_prefix [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1))
    (e₀ w₀ : Vector (Vector R (n + 1)) (n + 1))
    (roots₀ : Vector (Vector (Option (Fin n)) n) n)
    (savedCount m : Nat) (hm : m ≤ n)
    (hSettled : Settled p q e₀ w₀ roots₀ 1 0) :
    let result : Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector R (n + 1)) (n + 1) ×
        Vector (Vector (Option (Fin n)) n) n × Nat := Id.run do
      let mut e := e₀
      let mut w := w₀
      let mut root := roots₀
      let mut candidateCount := savedCount
      for hl : lengthOffset in [:m] do
        have hLengthOffset : lengthOffset < n := by
          have h : lengthOffset < m := hl.2.1
          omega
        let length := lengthOffset + 1
        for ha : a in [:n - length + 1] do
          have hStart : a < n - length + 1 := ha.2.1
          let b := a + length
          have hB : b ≤ n := by omega
          have hA : a < n := by omega
          let savedWeight := w[a][b - 1] + p[b - 1] + q[b]
          w := w.set a (w[a].set b savedWeight)
          let firstRoot : Fin n := ⟨a, hA⟩
          let firstCandidate := e[a][a] + e[a + 1][b] + savedWeight
          let initialBest : WithTop R :=
            if (firstCandidate : WithTop R) < ⊤ then firstCandidate else ⊤
          have finiteInitial : initialBest ≠ ⊤ := by simp [initialBest]
          let mut best := initialBest.untop finiteInitial
          let mut chosen := firstRoot
          candidateCount := candidateCount + 1
          for hr : rootOffset in [:length - 1] do
            have hRootOffset : rootOffset < length - 1 := hr.2.1
            let rootIndex := a + rootOffset + 1
            have hRoot : rootIndex < n := by omega
            have hLeft : rootIndex < n + 1 := by omega
            have hRight : rootIndex + 1 < n + 1 := by omega
            let candidate := e[a][rootIndex] + e[rootIndex + 1][b] + savedWeight
            if candidate < best then
              best := candidate
              chosen := ⟨rootIndex, hRoot⟩
            candidateCount := candidateCount + 1
          e := e.set a (e[a].set b best)
          root := root.set a (root[a].set (b - 1) (some chosen))
      return (e, w, root, candidateCount)
    Settled p q result.1 result.2.1 result.2.2.1 (m + 1) 0 := by
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, yield_if,
    List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure]
  convert (fold_order_invariant
    (fun item : {i : Nat // i ∈ List.range' 0 m} => item.val) _
    (fun i (state : Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector R (n + 1)) (n + 1) ×
      Vector (Vector (Option (Fin n)) n) n × Nat) =>
        Settled p q state.1 state.2.1 state.2.2.1 (i + 1) 0)
    ?_ (List.range' 0 m).attach 0 (by simp)
    (e₀, w₀, roots₀, savedCount) hSettled) using 1
  · simp
  · intro state item hState
    have hItem := List.mem_range'.mp item.property
    have hStarts := starts_prefix p q state.1 state.2.1 state.2.2.1
      state.2.2.2 (item.val + 1) (n - (item.val + 1) + 1)
      (by omega) (by omega) le_rfl hState
    dsimp only at hStarts
    have hNext := settled_next_length p q _ _ _ (item.val + 1) hStarts
    simpa only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, yield_if,
      List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure] using hNext

private theorem execute_settled [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) :
    let actual := execute p q
    Settled p q actual.1 actual.2.1 actual.2.2.1 (n + 1) 0 := by
  let e₀ := Vector.replicate (n + 1) (Vector.replicate (n + 1) (0 : R))
  let w₀ := Vector.replicate (n + 1) (Vector.replicate (n + 1) (0 : R))
  let roots₀ := Vector.replicate n
    (Vector.replicate n (none : Option (Fin n)))
  let initialized := Id.run do
    let mut e := e₀
    let mut w := w₀
    for hi : i in [:n + 1] do
      e := e.set i (e[i].set i q[i])
      w := w.set i (w[i].set i q[i])
    return (e, w)
  have hDiagonals := diagonal_prefix q e₀ w₀ (n + 1) le_rfl
  have hE : ∀ i : Fin (n + 1), initialized.1[i.val][i.val] = q[i.val] := by
    intro i
    simpa [initialized] using hDiagonals.1 i i
  have hW : ∀ i : Fin (n + 1), initialized.2[i.val][i.val] = q[i.val] := by
    intro i
    simpa [initialized] using hDiagonals.2 i i
  have hInitial := settled_of_diagonals p q initialized.1 initialized.2 roots₀ hE hW
  have hAll := lengths_prefix p q initialized.1 initialized.2 roots₀ 0 n le_rfl hInitial
  simpa only [execute, initialized, e₀, w₀, roots₀,
    Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, yield_if,
    List.forIn'_pure_yield_eq_foldl, pure_bind, Id.run_pure] using hAll

private theorem execute_table_complete [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) :
  let actual := execute p q
  (∀ i : Fin (n + 1), actual.1[i.val][i.val] = q[i.val]) ∧
    (∀ a b : Fin (n + 1), a.val ≤ b.val →
      actual.2.1[a.val][b.val] = intervalMass p q a.val b.val) ∧
    (∀ (a : Fin n) (b : Fin (n + 1)) (hab : a.val < b.val),
      CellSpec p q actual.1 actual.2.2.1 a b hab) := by
  let actual := execute p q
  have hSettled :
      Settled p q actual.1 actual.2.1 actual.2.2.1 (n + 1) 0 := by
    simpa [actual] using execute_settled p q
  refine ⟨hSettled.1, ?_, ?_⟩
  · intro a b hab
    exact hSettled.2.1 a b hab (Or.inl (by omega))
  · intro a b hab
    exact hSettled.2.2 a b hab (Or.inl (by omega))

end Cslib.Algorithms.Lean.OptimalBST
