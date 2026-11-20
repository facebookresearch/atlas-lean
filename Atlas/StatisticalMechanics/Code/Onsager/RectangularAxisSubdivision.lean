/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.TorusPrimitiveParity



namespace StatMech.Onsager

open BaseCase

theorem onsDirectionWord_stepOf_fst_sum (word : List (Fin 4)) :
    ((word.map stepOf).sum).1 = (word.map ons_dirExponentX).sum := by
  induction word with
  | nil => rfl
  | cons d tail ih =>
      simp only [List.map_cons, List.sum_cons, Prod.fst_add, ih]
      fin_cases d <;> rfl

theorem onsDirectionWord_stepOf_snd_sum (word : List (Fin 4)) :
    ((word.map stepOf).sum).2 = (word.map ons_dirExponentY).sum := by
  induction word with
  | nil => rfl
  | cons d tail ih =>
      simp only [List.map_cons, List.sum_cons, Prod.snd_add, ih]
      fin_cases d <;> rfl




def onsAnisotropicStepScale (width height : ℕ) (d : Fin 4) : ℕ :=
  if d = 0 ∨ d = 2 then height else width



def onsAnisotropicDirectionWord (width height : ℕ)
    (word : List (Fin 4)) : List (Fin 4) :=
  word.flatMap fun d ↦ List.replicate (onsAnisotropicStepScale width height d) d

@[simp] theorem onsAnisotropicDirectionWord_nil (width height : ℕ) :
    onsAnisotropicDirectionWord width height [] = [] := rfl

@[simp] theorem onsAnisotropicDirectionWord_cons
    (width height : ℕ) (d : Fin 4) (tail : List (Fin 4)) :
    onsAnisotropicDirectionWord width height (d :: tail) =
      List.replicate (onsAnisotropicStepScale width height d) d ++
        onsAnisotropicDirectionWord width height tail := rfl

@[simp] theorem onsAnisotropicStepScale_zero (width height : ℕ) :
    onsAnisotropicStepScale width height 0 = height := by
  simp [onsAnisotropicStepScale]

@[simp] theorem onsAnisotropicStepScale_one (width height : ℕ) :
    onsAnisotropicStepScale width height 1 = width := by
  simp [onsAnisotropicStepScale, show (1 : Fin 4) ≠ 0 by decide,
    show (1 : Fin 4) ≠ 2 by decide]

@[simp] theorem onsAnisotropicStepScale_two (width height : ℕ) :
    onsAnisotropicStepScale width height 2 = height := by
  simp [onsAnisotropicStepScale]

@[simp] theorem onsAnisotropicStepScale_three (width height : ℕ) :
    onsAnisotropicStepScale width height 3 = width := by
  simp [onsAnisotropicStepScale, show (3 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 2 by decide]

theorem onsAnisotropicDirectionWord_step_sum
    (width height : ℕ) (word : List (Fin 4)) :
    ((onsAnisotropicDirectionWord width height word).map stepOf).sum =
      ((height : ℤ) * ((word.map stepOf).sum).1,
        (width : ℤ) * ((word.map stepOf).sum).2) := by
  induction word with
  | nil => simp [Prod.ext_iff]
  | cons d tail ih =>
      simp only [onsAnisotropicDirectionWord_cons, List.map_append,
        List.sum_append, List.map_replicate, List.sum_replicate,
        List.map_cons, List.sum_cons, ih]
      fin_cases d <;>
        simp [stepOf, onsAnisotropicStepScale, Prod.ext_iff] <;> ring

theorem onsAnisotropicDirectionWord_exponentX_sum
    (width height : ℕ) (word : List (Fin 4)) :
    ((onsAnisotropicDirectionWord width height word).map
        ons_dirExponentX).sum =
      (height : ℤ) * (word.map ons_dirExponentX).sum := by
  induction word with
  | nil => simp
  | cons d tail ih =>
      rw [onsAnisotropicDirectionWord_cons, List.map_append,
        List.sum_append, List.map_replicate, List.sum_replicate, ih]
      fin_cases d <;>
        simp [onsAnisotropicStepScale, ons_dirExponentX] <;> ring

theorem onsAnisotropicDirectionWord_exponentY_sum
    (width height : ℕ) (word : List (Fin 4)) :
    ((onsAnisotropicDirectionWord width height word).map
        ons_dirExponentY).sum =
      (width : ℤ) * (word.map ons_dirExponentY).sum := by
  induction word with
  | nil => simp
  | cons d tail ih =>
      rw [onsAnisotropicDirectionWord_cons, List.map_append,
        List.sum_append, List.map_replicate, List.sum_replicate, ih]
      fin_cases d <;>
        simp [onsAnisotropicStepScale, ons_dirExponentY] <;> ring



def onsAnisotropicVertexEmbed (width height : ℕ)
    (p : Fin width × Fin height) :
    ZMod (width * height) × ZMod (width * height) :=
  ((height * p.1.val : ℕ), (width * p.2.val : ℕ))

theorem onsAnisotropicVertexEmbed_injective
    (width height : ℕ) [NeZero width] [NeZero height] :
    Function.Injective (onsAnisotropicVertexEmbed width height) := by
  have hwidth : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have hheight : 0 < height := Nat.pos_of_ne_zero (NeZero.ne height)
  intro p q hpq
  apply Prod.ext <;> apply Fin.ext
  · have hx := congrArg (fun z : ZMod (width * height) ×
        ZMod (width * height) ↦ z.1.val) hpq
    simp only [onsAnisotropicVertexEmbed] at hx
    rw [ZMod.val_natCast, ZMod.val_natCast] at hx
    have hpLt : height * p.1.val < width * height := by
      simpa [Nat.mul_comm] using
        (Nat.mul_lt_mul_left hheight).2 p.1.isLt
    have hqLt : height * q.1.val < width * height := by
      simpa [Nat.mul_comm] using
        (Nat.mul_lt_mul_left hheight).2 q.1.isLt
    rw [Nat.mod_eq_of_lt hpLt, Nat.mod_eq_of_lt hqLt] at hx
    exact Nat.eq_of_mul_eq_mul_left hheight hx
  · have hy := congrArg (fun z : ZMod (width * height) ×
        ZMod (width * height) ↦ z.2.val) hpq
    simp only [onsAnisotropicVertexEmbed] at hy
    rw [ZMod.val_natCast, ZMod.val_natCast] at hy
    have hpLt : width * p.2.val < width * height :=
      (Nat.mul_lt_mul_left hwidth).2 p.2.isLt
    have hqLt : width * q.2.val < width * height :=
      (Nat.mul_lt_mul_left hwidth).2 q.2.isLt
    rw [Nat.mod_eq_of_lt hpLt, Nat.mod_eq_of_lt hqLt] at hy
    exact Nat.eq_of_mul_eq_mul_left hwidth hy




theorem onsAnisotropicDirectionWord_preserves_winding
    (width height : ℕ) (word : List (Fin 4)) (mx my : ℤ)
    (hx : (word.map ons_dirExponentX).sum = (width : ℤ) * mx)
    (hy : (word.map ons_dirExponentY).sum = (height : ℤ) * my) :
    ((onsAnisotropicDirectionWord width height word).map
        ons_dirExponentX).sum = (width * height : ℕ) * mx ∧
      ((onsAnisotropicDirectionWord width height word).map
        ons_dirExponentY).sum = (width * height : ℕ) * my := by
  constructor
  · rw [onsAnisotropicDirectionWord_exponentX_sum, hx]
    push_cast
    ring
  · rw [onsAnisotropicDirectionWord_exponentY_sum, hy]
    push_cast
    ring



def onsDiagonalShearDirectionBlock (d : Fin 4) : List (Fin 4) :=
  match d.val with
  | 0 => [0, 1]
  | 1 => [0, 3]
  | 2 => [2, 3]
  | _ => [2, 1]


def onsDiagonalShearDirectionWord (word : List (Fin 4)) : List (Fin 4) :=
  word.flatMap onsDiagonalShearDirectionBlock

@[simp] theorem onsDiagonalShearDirectionWord_nil :
    onsDiagonalShearDirectionWord [] = [] := rfl

@[simp] theorem onsDiagonalShearDirectionWord_cons
    (d : Fin 4) (tail : List (Fin 4)) :
    onsDiagonalShearDirectionWord (d :: tail) =
      onsDiagonalShearDirectionBlock d ++
        onsDiagonalShearDirectionWord tail := rfl


def onsDirectionNonUturn (d e : Fin 4) : Prop := e ≠ d + 2

theorem onsDirectionNonUturn_self (d : Fin 4) :
    onsDirectionNonUturn d d := by
  fin_cases d <;> simp [onsDirectionNonUturn]

theorem onsDiagonalShearDirectionBlock_isChain (d : Fin 4) :
    List.IsChain onsDirectionNonUturn
      (onsDiagonalShearDirectionBlock d) := by
  fin_cases d <;> simp [onsDiagonalShearDirectionBlock,
    onsDirectionNonUturn]

theorem onsDiagonalShearDirectionBlock_bridge
    (d e : Fin 4) (hde : onsDirectionNonUturn d e) :
    ∀ a ∈ (onsDiagonalShearDirectionBlock d).getLast?,
      ∀ b ∈ (onsDiagonalShearDirectionBlock e).head?,
        onsDirectionNonUturn a b := by
  fin_cases d <;> fin_cases e <;>
    simp [onsDiagonalShearDirectionBlock, onsDirectionNonUturn] at hde ⊢



theorem onsDiagonalShearDirectionWord_isChain
    (word : List (Fin 4))
    (hchain : List.IsChain onsDirectionNonUturn word) :
    List.IsChain onsDirectionNonUturn
      (onsDiagonalShearDirectionWord word) := by
  induction word with
  | nil => exact List.IsChain.nil
  | cons d tail ih =>
      rw [onsDiagonalShearDirectionWord_cons]
      apply (onsDiagonalShearDirectionBlock_isChain d).append
        (ih (List.isChain_cons.mp hchain).2)
      cases tail with
      | nil => simp
      | cons e rest =>
          have hhead : (onsDiagonalShearDirectionWord (e :: rest)).head? =
              (onsDiagonalShearDirectionBlock e).head? := by
            rw [onsDiagonalShearDirectionWord_cons]
            fin_cases e <;> rfl
          rw [hhead]
          exact onsDiagonalShearDirectionBlock_bridge d e
            (List.isChain_cons_cons.mp hchain).1

theorem onsReplicateDirection_isChain (d : Fin 4) (n : ℕ) :
    List.IsChain onsDirectionNonUturn (List.replicate n d) := by
  induction n with
  | zero => exact List.IsChain.nil
  | succ n ih =>
      rw [List.replicate_succ]
      apply List.IsChain.cons ih
      simp only [List.head?_replicate]
      split_ifs
      · simp
      · simpa using onsDirectionNonUturn_self d

theorem onsReplicateDirection_bridge
    (d e : Fin 4) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hde : onsDirectionNonUturn d e) :
    ∀ a ∈ (List.replicate m d).getLast?,
      ∀ b ∈ (List.replicate n e).head?,
        onsDirectionNonUturn a b := by
  simp [List.getLast?_replicate, List.head?_replicate, hm.ne', hn.ne', hde]



theorem onsAnisotropicDirectionWord_isChain
    (width height : ℕ)
    (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4))
    (hchain : List.IsChain onsDirectionNonUturn word) :
    List.IsChain onsDirectionNonUturn
      (onsAnisotropicDirectionWord width height word) := by
  have hscale (d : Fin 4) : 0 < onsAnisotropicStepScale width height d := by
    fin_cases d <;> simp [onsAnisotropicStepScale, hwidth, hheight]
  induction word with
  | nil => exact List.IsChain.nil
  | cons d tail ih =>
      rw [onsAnisotropicDirectionWord_cons]
      apply (onsReplicateDirection_isChain d _).append
        (ih (List.isChain_cons.mp hchain).2)
      cases tail with
      | nil => simp
      | cons e rest =>
          simpa [onsAnisotropicDirectionWord_cons,
            List.head?_replicate, (hscale e).ne'] using
            (onsReplicateDirection_bridge d e _ _ (hscale d) (hscale e)
              (List.isChain_cons_cons.mp hchain).1)

theorem onsDiagonalShearDirectionWord_head?_mem
    (word : List (Fin 4)) {a : Fin 4}
    (ha : a ∈ (onsDiagonalShearDirectionWord word).head?) :
    ∃ d ∈ word.head?,
      a ∈ (onsDiagonalShearDirectionBlock d).head? := by
  cases word with
  | nil => simp at ha
  | cons d tail =>
      refine ⟨d, by simp, ?_⟩
      fin_cases d <;>
        simpa [onsDiagonalShearDirectionWord_cons,
          onsDiagonalShearDirectionBlock] using ha

theorem onsDiagonalShearDirectionWord_getLast?_mem
    (word : List (Fin 4)) {a : Fin 4}
    (ha : a ∈ (onsDiagonalShearDirectionWord word).getLast?) :
    ∃ d ∈ word.getLast?,
      a ∈ (onsDiagonalShearDirectionBlock d).getLast? := by
  induction word with
  | nil => simp at ha
  | cons d tail ih =>
      cases tail with
      | nil =>
          refine ⟨d, by simp, ?_⟩
          simpa [onsDiagonalShearDirectionWord_cons] using ha
      | cons e rest =>
          have hne : onsDiagonalShearDirectionWord (e :: rest) ≠ [] := by
            fin_cases e <;>
              simp [onsDiagonalShearDirectionWord_cons,
                onsDiagonalShearDirectionBlock]
          have ha' : a ∈
              (onsDiagonalShearDirectionWord (e :: rest)).getLast? := by
            rw [onsDiagonalShearDirectionWord_cons,
              List.getLast?_append_of_ne_nil _ hne] at ha
            exact ha
          obtain ⟨x, hxlast, hax⟩ := ih ha'
          exact ⟨x, by simpa using hxlast, hax⟩

theorem onsAnisotropicDirectionWord_head?_mem
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4)) {a : Fin 4}
    (ha : a ∈ (onsAnisotropicDirectionWord width height word).head?) :
    ∃ d ∈ word.head?,
      a ∈ (List.replicate
        (onsAnisotropicStepScale width height d) d).head? := by
  have hscale (d : Fin 4) : 0 < onsAnisotropicStepScale width height d := by
    fin_cases d <;> simp [onsAnisotropicStepScale, hwidth, hheight]
  cases word with
  | nil => simp at ha
  | cons d tail =>
      refine ⟨d, by simp, ?_⟩
      simpa [onsAnisotropicDirectionWord_cons, List.head?_replicate,
        (hscale d).ne'] using ha

theorem onsAnisotropicDirectionWord_getLast?_mem
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4)) {a : Fin 4}
    (ha : a ∈ (onsAnisotropicDirectionWord width height word).getLast?) :
    ∃ d ∈ word.getLast?,
      a ∈ (List.replicate
        (onsAnisotropicStepScale width height d) d).getLast? := by
  have hscale (d : Fin 4) : 0 < onsAnisotropicStepScale width height d := by
    fin_cases d <;> simp [onsAnisotropicStepScale, hwidth, hheight]
  induction word with
  | nil => simp at ha
  | cons d tail ih =>
      cases tail with
      | nil =>
          refine ⟨d, by simp, ?_⟩
          simpa [onsAnisotropicDirectionWord_cons] using ha
      | cons e rest =>
          have hne :
              onsAnisotropicDirectionWord width height (e :: rest) ≠ [] := by
            intro hnil
            have hlen := congrArg List.length hnil
            simp [onsAnisotropicDirectionWord_cons,
              (hscale e).ne'] at hlen
          have ha' : a ∈
              (onsAnisotropicDirectionWord width height
                (e :: rest)).getLast? := by
            rw [onsAnisotropicDirectionWord_cons,
              List.getLast?_append_of_ne_nil _ hne] at ha
            exact ha
          obtain ⟨x, hxlast, hax⟩ := ih ha'
          exact ⟨x, by simpa using hxlast, hax⟩



def onsCyclicDirectionNonUturn (word : List (Fin 4)) : Prop :=
  List.IsChain onsDirectionNonUturn word ∧
    ∀ a ∈ word.getLast?, ∀ b ∈ word.head?, onsDirectionNonUturn a b



theorem onsCyclicDirectionNonUturn_ofFn
    {n : ℕ} [NeZero n] (dir : Fin n → Fin 4)
    (hnu : ∀ k : Fin n, onsDirectionNonUturn (dir k) (dir (k + 1))) :
    onsCyclicDirectionNonUturn (List.ofFn dir) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  constructor
  · rw [List.isChain_ofFn]
    intro i hi
    let k : Fin (m + 1) := ⟨i, by omega⟩
    have hk : k ≠ Fin.last m := by
      intro h
      have := Fin.mk.inj_iff.mp h
      omega
    have hnext : k + 1 = ⟨i + 1, by omega⟩ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last k) hk)
    simpa [k, hnext] using hnu k
  · intro a ha b hb
    rw [List.getLast?_eq_getLast (by simp), List.getLast_ofFn] at ha
    simp only [Option.mem_def, Option.some.injEq] at ha
    rw [List.ofFn_succ] at hb
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst a
    subst b
    simpa using hnu (Fin.last m)

theorem onsCyclicDirectionNonUturn_ofFn_apply
    {n : ℕ} [NeZero n] (dir : Fin n → Fin 4)
    (hcyclic : onsCyclicDirectionNonUturn (List.ofFn dir)) :
    ∀ k : Fin n, onsDirectionNonUturn (dir k) (dir (k + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  intro k
  by_cases hk : k = Fin.last m
  · subst k
    apply hcyclic.2 (dir (Fin.last m))
    · rw [List.getLast?_eq_getLast (by simp), List.getLast_ofFn]
      simp only [Option.mem_def, Option.some.injEq]
      apply congrArg dir
      apply Fin.ext
      simp
    · rw [List.ofFn_succ]
      simp
  · have hklt : k.val < m := by
      have hle := Fin.le_last k
      exact lt_of_le_of_ne hle (fun h => hk (Fin.ext h))
    have hchain := hcyclic.1
    rw [List.isChain_ofFn] at hchain
    have h := hchain k.val (by omega)
    have hnext : k + 1 = ⟨k.val + 1, by omega⟩ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt (by simpa using hklt)
    simpa [hnext] using h

theorem onsDirectionNonUturn_comm (d e : Fin 4) :
    onsDirectionNonUturn d e ↔ onsDirectionNonUturn e d := by
  fin_cases d <;> fin_cases e <;> simp [onsDirectionNonUturn]




noncomputable def onsDirectionWordTorusDart
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length] :
    Fin word.length → ons_Dart L := by
  let dir : Fin word.length → Fin 4 := word.get
  exact fun k ↦
    (ons_reduceSite L (BaseCase.pos dir (-k)), dir (-k))

@[simp] theorem onsDirectionWordTorusDart_direction
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length]
    (k : Fin word.length) :
    (onsDirectionWordTorusDart L word k).2 = word.get (-k) := by
  simp [onsDirectionWordTorusDart]



theorem onsDirectionWordTorusDart_valid
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length]
    (mx my : ℤ)
    (hdisp : (word.map stepOf).sum = ((L : ℤ) * mx, (L : ℤ) * my)) :
    ∀ k : Fin word.length,
      (onsDirectionWordTorusDart L word k).1 =
        ons_dirStep L
          (onsDirectionWordTorusDart L word (k + 1)).2
          (onsDirectionWordTorusDart L word (k + 1)).1 := by
  let dir : Fin word.length → Fin 4 := word.get
  have htotal : ∑ i, stepOf (dir i) = ((L : ℤ) * mx, (L : ℤ) * my) := by
    rw [← List.sum_ofFn]
    change (List.ofFn fun i => stepOf (word.get i)).sum = _
    rw [show (List.ofFn fun i => stepOf (word.get i)) =
      word.map stepOf by
        simpa [List.get_eq_getElem] using
          (List.ofFn_getElem_eq_map word stepOf)]
    exact hdisp
  intro k
  change ons_reduceSite L (BaseCase.pos dir (-k)) =
    ons_dirStep L (dir (-(k + 1)))
      (ons_reduceSite L (BaseCase.pos dir (-(k + 1))))
  have hj : -(k + 1) + 1 = -k := by abel
  rw [← hj]
  cases word with
  | nil => exact False.elim ((NeZero.ne 0) rfl)
  | cons a tail =>
      by_cases hjlast : -(k + 1) = Fin.last tail.length
      · rw [hjlast]
        rw [Fin.last_add_one, NoDoubleWind.pos_zero]
        rw [← ons_reduceSite_add_step]
        rw [ons_pos_last_add_step]
        calc
          ons_reduceSite L 0 =
              ons_reduceSite L ((L : ℤ) * mx, (L : ℤ) * my) := by
                simp [ons_reduceSite]
          _ = ons_reduceSite L (∑ i, stepOf (dir i)) :=
            (congrArg (ons_reduceSite L) htotal).symm
      · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjlast
        rw [← hi]
        have hisucc : i.castSucc + 1 = i.succ := by
          apply Fin.ext
          simp
        rw [hisucc, ons_pos_succ_cast, ons_reduceSite_add_step]

theorem onsDirectionWordTorusDart_nonUturn
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length]
    (hcyclic : onsCyclicDirectionNonUturn word) :
    ∀ k : Fin word.length,
      (onsDirectionWordTorusDart L word k).2 ≠
        (onsDirectionWordTorusDart L word (k + 1)).2 + 2 := by
  have hword : List.ofFn word.get = word := List.ofFn_get word
  have hcyclic' : onsCyclicDirectionNonUturn (List.ofFn word.get) := by
    rwa [hword]
  intro k
  simp only [onsDirectionWordTorusDart_direction]
  change onsDirectionNonUturn (word.get (-(k + 1)))
    (word.get (-k))
  have h := onsCyclicDirectionNonUturn_ofFn_apply word.get hcyclic' (-(k + 1))
  have hidx : -(k + 1) + 1 = -k := by abel
  rw [hidx] at h
  exact h

theorem onsDirectionWordTorusDart_exponentX_sum
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length] :
    (∑ k, ons_dirExponentX
      (onsDirectionWordTorusDart L word k).2) =
      (word.map ons_dirExponentX).sum := by
  calc
    _ = ∑ k, ons_dirExponentX (word.get (-k)) := by simp
    _ = ∑ k, ons_dirExponentX (word.get k) :=
      Equiv.sum_comp (Equiv.neg (Fin word.length))
        (fun k ↦ ons_dirExponentX (word.get k))
    _ = _ := by
      rw [← List.sum_ofFn]
      congr 1
      simpa [List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map word ons_dirExponentX)

theorem onsDirectionWordTorusDart_exponentY_sum
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length] :
    (∑ k, ons_dirExponentY
      (onsDirectionWordTorusDart L word k).2) =
      (word.map ons_dirExponentY).sum := by
  calc
    _ = ∑ k, ons_dirExponentY (word.get (-k)) := by simp
    _ = ∑ k, ons_dirExponentY (word.get k) :=
      Equiv.sum_comp (Equiv.neg (Fin word.length))
        (fun k ↦ ons_dirExponentY (word.get k))
    _ = _ := by
      rw [← List.sum_ofFn]
      congr 1
      simpa [List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map word ons_dirExponentY)



theorem onsDiagonalShearDirectionWord_cyclicNonUturn
    (word : List (Fin 4))
    (hcyclic : onsCyclicDirectionNonUturn word) :
    onsCyclicDirectionNonUturn (onsDiagonalShearDirectionWord word) := by
  refine ⟨onsDiagonalShearDirectionWord_isChain word hcyclic.1, ?_⟩
  intro a ha b hb
  obtain ⟨d, hdlast, had⟩ :=
    onsDiagonalShearDirectionWord_getLast?_mem word ha
  obtain ⟨e, hehead, hbe⟩ :=
    onsDiagonalShearDirectionWord_head?_mem word hb
  exact onsDiagonalShearDirectionBlock_bridge d e
    (hcyclic.2 d hdlast e hehead) a had b hbe



theorem onsAnisotropicDirectionWord_cyclicNonUturn
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4))
    (hcyclic : onsCyclicDirectionNonUturn word) :
    onsCyclicDirectionNonUturn
      (onsAnisotropicDirectionWord width height word) := by
  refine ⟨onsAnisotropicDirectionWord_isChain width height hwidth hheight
    word hcyclic.1, ?_⟩
  intro a ha b hb
  obtain ⟨d, hdlast, had⟩ := onsAnisotropicDirectionWord_getLast?_mem
    width height hwidth hheight word ha
  obtain ⟨e, hehead, hbe⟩ := onsAnisotropicDirectionWord_head?_mem
    width height hwidth hheight word hb
  have hscale (x : Fin 4) : 0 < onsAnisotropicStepScale width height x := by
    fin_cases x <;> simp [onsAnisotropicStepScale, hwidth, hheight]
  exact onsReplicateDirection_bridge d e _ _ (hscale d) (hscale e)
    (hcyclic.2 d hdlast e hehead) a had b hbe

theorem onsDiagonalShearDirectionBlock_step_sum (d : Fin 4) :
    ((onsDiagonalShearDirectionBlock d).map stepOf).sum =
      ((stepOf d).1 + (stepOf d).2, (stepOf d).1 - (stepOf d).2) := by
  fin_cases d <;> rfl

theorem onsDiagonalShearDirectionWord_step_sum (word : List (Fin 4)) :
    ((onsDiagonalShearDirectionWord word).map stepOf).sum =
      (((word.map stepOf).sum).1 + ((word.map stepOf).sum).2,
        ((word.map stepOf).sum).1 - ((word.map stepOf).sum).2) := by
  induction word with
  | nil => simp [onsDiagonalShearDirectionWord, Prod.ext_iff]
  | cons d tail ih =>
      rw [onsDiagonalShearDirectionWord, List.flatMap_cons,
        List.map_append, List.sum_append,
        onsDiagonalShearDirectionBlock_step_sum]
      change _ +
        ((onsDiagonalShearDirectionWord tail).map stepOf).sum = _
      rw [ih]
      apply Prod.ext <;> simp <;> ring





def onsRectangularShearSubdivisionWord (width height : ℕ)
    (word : List (Fin 4)) : List (Fin 4) :=
  onsAnisotropicDirectionWord (4 * width) (2 * height)
    (onsDiagonalShearDirectionWord word)



theorem onsRectangularShearSubdivisionWord_cyclicNonUturn
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4))
    (hcyclic : onsCyclicDirectionNonUturn word) :
    onsCyclicDirectionNonUturn
      (onsRectangularShearSubdivisionWord width height word) := by
  unfold onsRectangularShearSubdivisionWord
  apply onsAnisotropicDirectionWord_cyclicNonUturn
      (4 * width) (2 * height) (by positivity) (by positivity)
  exact onsDiagonalShearDirectionWord_cyclicNonUturn word hcyclic

theorem onsRectangularShearSubdivisionWord_preserves_deck_winding
    (width height : ℕ) (word : List (Fin 4)) (x y : ℤ)
    (hdisp : (word.map stepOf).sum =
      ((2 * width : ℕ) * x + (height : ℤ) * y,
        (2 * width : ℕ) * x - (height : ℤ) * y)) :
    ((onsRectangularShearSubdivisionWord width height word).map
        ons_dirExponentX).sum = (8 * width * height : ℕ) * x ∧
      ((onsRectangularShearSubdivisionWord width height word).map
        ons_dirExponentY).sum = (8 * width * height : ℕ) * y := by
  have hshear := onsDiagonalShearDirectionWord_step_sum word
  rw [hdisp] at hshear
  have hx : ((onsDiagonalShearDirectionWord word).map
      ons_dirExponentX).sum = (4 * width : ℕ) * x := by
    have h := congrArg Prod.fst hshear
    rw [onsDirectionWord_stepOf_fst_sum] at h
    calc
      _ = ((2 * width : ℕ) : ℤ) * x + (height : ℤ) * y +
          (((2 * width : ℕ) : ℤ) * x - (height : ℤ) * y) := by
        simpa only [Prod.fst, Prod.snd] using h
      _ = (4 * width : ℕ) * x := by push_cast; ring
  have hy : ((onsDiagonalShearDirectionWord word).map
      ons_dirExponentY).sum = (2 * height : ℕ) * y := by
    have h := congrArg Prod.snd hshear
    rw [onsDirectionWord_stepOf_snd_sum] at h
    calc
      _ = ((2 * width : ℕ) : ℤ) * x + (height : ℤ) * y -
          (((2 * width : ℕ) : ℤ) * x - (height : ℤ) * y) := by
        simpa only [Prod.fst, Prod.snd] using h
      _ = (2 * height : ℕ) * y := by push_cast; ring
  have hscaled := onsAnisotropicDirectionWord_preserves_winding
    (4 * width) (2 * height) (onsDiagonalShearDirectionWord word) x y hx hy
  simpa [onsRectangularShearSubdivisionWord, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using hscaled

end StatMech.Onsager
