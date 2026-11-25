/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.RingTheory.Kaehler.DeRhamDifferential.OneForm
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Exterior presentations of the de Rham differential

The signed derivative of an ordered list of one-forms respects the
alternating relations and their span. It therefore descends from the free
presentation to a base-linear map on each exterior power of the Kähler
module, taking degree `n` to degree `n + 1`.
-/

public section
noncomputable section
universe u v
variable (K : Type u) (A : Type v) [CommRing K] [CommRing A] [Algebra K A]

namespace KaehlerDifferential.DeRham

/-- The ordered exterior product of a finite list of original one-forms. -/
def orderedProduct : List (W K A) → E K A
  | [] => 1
  | w :: ws => ExteriorAlgebra.ι A w * orderedProduct ws

/-- The signed derivative of an ordered list of original one-forms. -/
def orderedDifferential : List (W K A) → E K A
  | [] => 0
  | w :: ws => differentialOneToExterior K A w * orderedProduct K A ws -
      ExteriorAlgebra.ι A w * orderedDifferential ws

private lemma orderedProduct_nil : orderedProduct K A [] = 1 := rfl
private lemma orderedProduct_cons (w : W K A) (ws : List (W K A)) :
    orderedProduct K A (w :: ws) = ExteriorAlgebra.ι A w * orderedProduct K A ws := rfl
private lemma orderedDifferential_nil : orderedDifferential K A [] = 0 := rfl
private lemma orderedDifferential_cons (w : W K A) (ws : List (W K A)) :
    orderedDifferential K A (w :: ws) =
      differentialOneToExterior K A w * orderedProduct K A ws -
        ExteriorAlgebra.ι A w * orderedDifferential K A ws := rfl

attribute [local simp] orderedProduct_nil orderedProduct_cons
  orderedDifferential_nil orderedDifferential_cons

lemma orderedProduct_ofFn {n : ℕ} (v : Fin n → W K A) :
    orderedProduct K A (List.ofFn v) = ExteriorAlgebra.ιMulti A n v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, orderedProduct_cons, ih]
    exact (ExteriorAlgebra.ιMulti_succ_apply v).symm

lemma orderedDifferential_closed (ws : List A) :
    orderedDifferential K A (ws.map (D K A)) = 0 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    simp [differentialOneToExterior_D, ih]

/-- The ordered derivative expressed on a finite tuple of one-forms. -/
def tupleDifferential (n : ℕ) (v : Fin n → W K A) : E K A :=
  orderedDifferential K A (List.ofFn v)

/-- The base-linear coefficient operator for a fixed exterior tuple. -/
def coefficientDegree (n : ℕ) (v : Fin n → W K A) : A →ₗ[K] E K A where
  toFun a := ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ιMulti A n v +
    a • tupleDifferential K A n v
  map_add' a b := by simp [add_mul, add_smul]; abel
  map_smul' r a := by
    change ExteriorAlgebra.ι A (D K A (r • a)) * ExteriorAlgebra.ιMulti A n v +
        (r • a) • tupleDifferential K A n v =
      r • (ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ιMulti A n v +
        a • tupleDifferential K A n v)
    rw [Derivation.map_smul, LinearMap.map_smul_of_tower,
      smul_mul_assoc, smul_assoc, smul_add]



/-- The base-linear derivative on the actual free exterior presentation. -/
def freeDifferentialDegree (n : ℕ) : ((Fin n → W K A) →₀ A) →ₗ[K] E K A :=
  Finsupp.lsum K (coefficientDegree K A n : (Fin n → W K A) → A →ₗ[K] E K A)

/-- The original exterior presentation map into the exterior algebra. -/
def presentationDegree (n : ℕ) : ((Fin n → W K A) →₀ A) →ₗ[A] E K A :=
  Finsupp.linearCombination A (ExteriorAlgebra.ιMulti A n)

@[simp] lemma freeDifferentialDegree_single (n : ℕ) (v : Fin n → W K A) (a : A) :
    freeDifferentialDegree K A n (Finsupp.single v a) =
      ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ιMulti A n v +
        a • tupleDifferential K A n v := by
  change Finsupp.lsum K (coefficientDegree K A n :
    (Fin n → W K A) → A →ₗ[K] E K A) (Finsupp.single v a) = _
  rw [Finsupp.lsum_single]
  rfl

@[simp] lemma presentationDegree_single (n : ℕ) (v : Fin n → W K A) (a : A) :
    presentationDegree K A n (Finsupp.single v a) = a • ExteriorAlgebra.ιMulti A n v := by
  exact Finsupp.linearCombination_single _ _ _

lemma freeDifferentialDegree_smul (n : ℕ) (a : A) (q : (Fin n → W K A) →₀ A) :
    freeDifferentialDegree K A n (a • q) =
      ExteriorAlgebra.ι A (D K A a) * presentationDegree K A n q +
        a • freeDifferentialDegree K A n q := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr =>
    simp only [smul_add, map_add, hq, hr, mul_add]
    abel
  | single v b =>
    simp only [Finsupp.smul_single, smul_eq_mul, freeDifferentialDegree_single,
      presentationDegree_single, Derivation.leibniz, map_add, map_smul,
      add_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel


lemma orderedProduct_add_slot (before suffix : List (W K A)) (x y : W K A) :
    orderedProduct K A (before ++ (x + y) :: suffix) =
      orderedProduct K A (before ++ x :: suffix) +
        orderedProduct K A (before ++ y :: suffix) := by
  induction before with
  | nil => simp [add_mul]
  | cons w before ih => simp [ih, mul_add]

lemma orderedDifferential_add_slot (before suffix : List (W K A)) (x y : W K A) :
    orderedDifferential K A (before ++ (x + y) :: suffix) =
      orderedDifferential K A (before ++ x :: suffix) +
        orderedDifferential K A (before ++ y :: suffix) := by
  induction before with
  | nil =>
    simp only [List.nil_append, orderedDifferential_cons, map_add, add_mul]
    abel
  | cons w before ih =>
    simp only [List.cons_append, orderedDifferential_cons, orderedProduct_add_slot,
      ih, mul_add]
    abel


lemma orderedProduct_append (xs ys : List (W K A)) :
    orderedProduct K A (xs ++ ys) = orderedProduct K A xs * orderedProduct K A ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

lemma orderedProduct_smul_slot (before suffix : List (W K A)) (a : A) (x : W K A) :
    orderedProduct K A (before ++ (a • x) :: suffix) =
      a • orderedProduct K A (before ++ x :: suffix) := by
  induction before with
  | nil => simp
  | cons w before ih => simp [ih]

lemma oneForm_mul_orderedProduct_sign (w : W K A) (xs : List (W K A)) :
    ExteriorAlgebra.ι A w * orderedProduct K A xs =
      (-1 : ℤˣ) ^ xs.length •
        (orderedProduct K A xs * ExteriorAlgebra.ι A w) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, orderedProduct_cons]
    rw [← mul_assoc]
    have hs : ExteriorAlgebra.ι A w * ExteriorAlgebra.ι A x =
        -(ExteriorAlgebra.ι A x * ExteriorAlgebra.ι A w) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap w x)
    rw [hs, neg_mul, mul_assoc, ih, mul_smul_comm]
    simp [pow_succ, mul_assoc]


lemma orderedDifferential_smul_slot (before suffix : List (W K A)) (a : A) (x : W K A) :
    orderedDifferential K A (before ++ (a • x) :: suffix) =
      ExteriorAlgebra.ι A (D K A a) * orderedProduct K A (before ++ x :: suffix) +
        a • orderedDifferential K A (before ++ x :: suffix) := by
  induction before with
  | nil =>
    simp only [List.nil_append, orderedDifferential_cons, orderedProduct_cons,
      differentialOneToExterior_smul, map_smul, add_mul, smul_mul_assoc, smul_sub]
    rw [mul_assoc]
    abel
  | cons w before ih =>
    simp only [List.cons_append, orderedDifferential_cons, orderedProduct_cons,
      orderedProduct_smul_slot, ih, mul_smul_comm, mul_add, smul_sub]
    have hs : ExteriorAlgebra.ι A w * ExteriorAlgebra.ι A (D K A a) =
        -(ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ι A w) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap w (D K A a))
    rw [← mul_assoc (ExteriorAlgebra.ι A w) (ExteriorAlgebra.ι A (D K A a)),
      hs, neg_mul, mul_assoc]
    abel


lemma degreeTwo_commutes_oneForm {q : E K A}
    (hq : q ∈ ExteriorAlgebra.exteriorPower A 2 (W K A)) (w : W K A) :
    q * ExteriorAlgebra.ι A w = ExteriorAlgebra.ι A w * q := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hq
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨v, rfl⟩
    have h := ExteriorAlgebra.ι_mul_ιMulti_anticomm A w v
    simpa using h.symm
  · simp
  · intro a b ha hb iha ihb
    rw [add_mul, mul_add, iha, ihb]
  · intro a b hb ih
    rw [smul_mul_assoc, mul_smul_comm, ih]

lemma derivative_commutes_oneForm (x y : W K A) :
    differentialOneToExterior K A x * ExteriorAlgebra.ι A y =
      ExteriorAlgebra.ι A y * differentialOneToExterior K A x :=
  degreeTwo_commutes_oneForm K A (differentialOneToExterior_mem_two K A x) y

lemma orderedDifferential_repeat_adjacent (before suffix : List (W K A)) (x : W K A) :
    orderedDifferential K A (before ++ x :: x :: suffix) = 0 := by
  induction before with
  | nil =>
    simp only [List.nil_append, orderedDifferential_cons, orderedProduct_cons, mul_sub]
    simp only [← mul_assoc]
    rw [ExteriorAlgebra.ι_sq_zero, zero_mul, sub_zero,
      derivative_commutes_oneForm]
    exact sub_self _
  | cons w before ih =>
    simp only [List.cons_append, orderedDifferential_cons, ih, mul_zero, sub_zero]
    have hz : orderedProduct K A (before ++ x :: x :: suffix) = 0 := by
      rw [orderedProduct_append]
      simp only [orderedProduct_cons, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
        zero_mul, mul_zero]
    rw [hz, mul_zero]

lemma orderedDifferential_swap_adjacent (before suffix : List (W K A)) (x y : W K A) :
    orderedDifferential K A (before ++ x :: y :: suffix) =
      -orderedDifferential K A (before ++ y :: x :: suffix) := by
  induction before with
  | nil =>
    simp only [List.nil_append, orderedDifferential_cons, orderedProduct_cons,
      mul_sub, ← mul_assoc]
    have hxy : ExteriorAlgebra.ι A x * ExteriorAlgebra.ι A y =
        -(ExteriorAlgebra.ι A y * ExteriorAlgebra.ι A x) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)
    rw [hxy, neg_mul, derivative_commutes_oneForm, derivative_commutes_oneForm]
    abel
  | cons w before ih =>
    simp only [List.cons_append, orderedDifferential_cons, ih, mul_neg]
    have hp : orderedProduct K A (before ++ x :: y :: suffix) =
        -orderedProduct K A (before ++ y :: x :: suffix) := by
      rw [orderedProduct_append, orderedProduct_append]
      simp only [orderedProduct_cons]
      have hxy : ExteriorAlgebra.ι A x * ExteriorAlgebra.ι A y =
          -(ExteriorAlgebra.ι A y * ExteriorAlgebra.ι A x) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)
      simp only [← mul_assoc] at *
      have hxy' := congrArg (fun z : E K A =>
        orderedProduct K A before * (z * orderedProduct K A suffix)) hxy
      simpa only [mul_neg, neg_mul, ← mul_assoc] using hxy'
    rw [hp, mul_neg]
    abel


lemma orderedDifferential_move_repeat (before middle suffix : List (W K A)) (x : W K A) :
    orderedDifferential K A (before ++ x :: (middle ++ x :: suffix)) = 0 := by
  induction middle generalizing before with
  | nil => exact orderedDifferential_repeat_adjacent K A before suffix x
  | cons y middle ih =>
    have hswap := orderedDifferential_swap_adjacent K A before (middle ++ x :: suffix) x y
    simp only [List.cons_append] at ⊢
    rw [hswap]
    have hz := ih (before ++ [y])
    simpa only [List.append_assoc, List.singleton_append] using neg_eq_zero.mpr hz

lemma orderedDifferential_eq_zero_of_not_nodup (ws : List (W K A))
    (hw : ¬ws.Nodup) : orderedDifferential K A ws = 0 := by
  induction ws with
  | nil => exact (hw (by simp)).elim
  | cons x ws ih =>
    by_cases hmem : x ∈ ws
    · obtain ⟨middle, suffix, hws⟩ := List.mem_iff_append.mp hmem
      rw [hws]
      exact orderedDifferential_move_repeat K A [] middle suffix x
    · have hn : ¬ws.Nodup := by
        intro hn
        exact hw (List.nodup_cons.mpr ⟨hmem, hn⟩)
      simp only [orderedDifferential_cons, ih hn, mul_zero, sub_zero]
      have hp : orderedProduct K A ws = 0 := by
        rw [← List.ofFn_get ws, orderedProduct_ofFn]
        apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
        intro hv
        have hnodup : (List.ofFn ws.get).Nodup := (List.nodup_ofFn).mpr hv
        exact hn (List.ofFn_get ws ▸ hnodup)
      rw [hp, mul_zero]


lemma tupleDifferential_add_update (n : ℕ) (v : Fin n → W K A) (i : Fin n) (x y : W K A) :
    tupleDifferential K A n (Function.update v i (x + y)) =
      tupleDifferential K A n (Function.update v i x) +
        tupleDifferential K A n (Function.update v i y) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      unfold tupleDifferential
      simp only [List.ofFn_succ]
      have hu (z : W K A) :
          List.ofFn (fun j : Fin n => Function.update v 0 z j.succ) =
            List.ofFn (fun j : Fin n => v j.succ) := by
        congr 1
      simp only [Function.update_self, hu, orderedDifferential_cons, map_add, add_mul]
      abel
    | succ i =>
      unfold tupleDifferential
      simp only [List.ofFn_succ]
      have hu (z : W K A) :
          List.ofFn (fun j : Fin n => Function.update v i.succ z j.succ) =
            List.ofFn (Function.update (v ∘ Fin.succ) i z) := by
        congr 1
        funext j
        simp [Function.update_apply]
      simp only [hu, Function.update_of_ne (Fin.succ_ne_zero i).symm,
        orderedDifferential_cons]
      have hd := ih (v ∘ Fin.succ) i
      unfold tupleDifferential at hd
      rw [hd]
      have hp : orderedProduct K A (List.ofFn (Function.update (v ∘ Fin.succ) i (x + y))) =
          orderedProduct K A (List.ofFn (Function.update (v ∘ Fin.succ) i x)) +
            orderedProduct K A (List.ofFn (Function.update (v ∘ Fin.succ) i y)) := by
        simp only [orderedProduct_ofFn]
        exact (ExteriorAlgebra.ιMulti A n).map_update_add (v ∘ Fin.succ) i x y
      rw [hp, mul_add, mul_add]
      abel

lemma tupleDifferential_eq_zero_of_eq (n : ℕ) (v : Fin n → W K A)
    (i j : Fin n) (hv : v i = v j) (hij : i ≠ j) : tupleDifferential K A n v = 0 := by
  apply orderedDifferential_eq_zero_of_not_nodup
  intro h
  have hinj := (List.nodup_ofFn).mp h
  exact hij (hinj hv)


lemma tupleDifferential_smul_update (n : ℕ) (v : Fin n → W K A) (i : Fin n)
    (a : A) (x : W K A) :
    tupleDifferential K A n (Function.update v i (a • x)) =
      ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ιMulti A n (Function.update v i x) +
        a • tupleDifferential K A n (Function.update v i x) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      unfold tupleDifferential
      simp only [List.ofFn_succ]
      have hu (z : W K A) :
          List.ofFn (fun j : Fin n => Function.update v 0 z j.succ) =
            List.ofFn (fun j : Fin n => v j.succ) := by
        congr 1
      simp only [Function.update_self, hu, orderedDifferential_cons,
        differentialOneToExterior_smul, map_smul, add_mul, smul_mul_assoc, smul_sub]
      have hp : ExteriorAlgebra.ιMulti A (n + 1) (Function.update v 0 x) =
          ExteriorAlgebra.ι A x * orderedProduct K A (List.ofFn (v ∘ Fin.succ)) := by
        rw [← orderedProduct_ofFn, List.ofFn_succ]
        simp [Function.comp_def]
      rw [hp, mul_assoc]
      simp only [Function.comp_def]
      abel
    | succ i =>
      unfold tupleDifferential
      simp only [List.ofFn_succ]
      have hu (z : W K A) :
          List.ofFn (fun j : Fin n => Function.update v i.succ z j.succ) =
            List.ofFn (Function.update (v ∘ Fin.succ) i z) := by
        congr 1
        funext j
        simp [Function.update_apply]
      simp only [hu, Function.update_of_ne (Fin.succ_ne_zero i).symm,
        orderedDifferential_cons]
      have hd := ih (v ∘ Fin.succ) i
      unfold tupleDifferential at hd
      rw [hd, mul_add, mul_smul_comm]
      have hp : orderedProduct K A (List.ofFn (Function.update (v ∘ Fin.succ) i (a • x))) =
          a • orderedProduct K A (List.ofFn (Function.update (v ∘ Fin.succ) i x)) := by
        rw [orderedProduct_ofFn, orderedProduct_ofFn]
        exact (ExteriorAlgebra.ιMulti A n).map_update_smul (v ∘ Fin.succ) i a x
      rw [hp, mul_smul_comm]
      have hfull : ExteriorAlgebra.ιMulti A (n + 1) (Function.update v i.succ x) =
          ExteriorAlgebra.ι A (v 0) *
            orderedProduct K A (List.ofFn (Function.update (v ∘ Fin.succ) i x)) := by
        rw [← orderedProduct_ofFn, List.ofFn_succ]
        simp [hu, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      rw [hfull]
      have hs : ExteriorAlgebra.ι A (v 0) * ExteriorAlgebra.ι A (D K A a) =
          -(ExteriorAlgebra.ι A (D K A a) * ExteriorAlgebra.ι A (v 0)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (v 0) (D K A a))
      rw [← mul_assoc (ExteriorAlgebra.ι A (v 0)) (ExteriorAlgebra.ι A (D K A a)),
        hs, neg_mul, mul_assoc, smul_sub]
      rw [orderedProduct_ofFn]
      abel

/-- The original degree-`n` exterior power of the Kähler module. -/
abbrev Forms (n : ℕ) := ExteriorAlgebra.exteriorPower A n (W K A)

/-- The free presentation of the exterior-power carrier. -/
noncomputable abbrev exteriorPresentation (n : ℕ) := exteriorPower.presentation A n (W K A)

/-- The original exterior presentation projection with its generator type explicit. -/
def presentationForms (n : ℕ) : ((Fin n → W K A) →₀ A) →ₗ[A] Forms K A n :=
  Finsupp.linearCombination A (exteriorPower.ιMulti A n)

/-- The relation function for the exterior-power presentation. -/
abbrev exteriorRelation (n : ℕ)
    (r : exteriorPower.presentation.Rels A (Fin n) (W K A)) : (Fin n → W K A) →₀ A :=
  (exteriorPower.presentation.relations A (Fin n) (W K A)).relation r

lemma presentationDegree_eq_subtype_comp (n : ℕ) :
    presentationDegree K A n = (Forms K A n).subtype.comp (presentationForms K A n) := by
  ext v
  simp [presentationDegree, presentationForms, LinearMap.comp_apply, Finsupp.lsingle_apply]

lemma presentationForms_relation (n : ℕ)
    (r : exteriorPower.presentation.Rels A (Fin n) (W K A)) :
    presentationForms K A n (exteriorRelation K A n r) = 0 := by
  cases r with
  | add v i x y =>
    change presentationForms K A n
      (Finsupp.single (Function.update v i x) 1 +
        Finsupp.single (Function.update v i y) 1 -
        Finsupp.single (Function.update v i (x + y)) 1) = 0
    simp only [map_sub, map_add, presentationForms, Finsupp.linearCombination_single,
      one_smul, AlternatingMap.map_update_add]
    abel
  | smul v i a x =>
    change presentationForms K A n
      (Finsupp.single (Function.update v i (a • x)) 1 -
        a • Finsupp.single (Function.update v i x) 1) = 0
    simp [presentationForms, AlternatingMap.map_update_smul]
  | alt v i j hv hij =>
    change presentationForms K A n (Finsupp.single v 1) = 0
    simp only [presentationForms, Finsupp.linearCombination_single, one_smul]
    exact (exteriorPower.ιMulti A n).map_eq_zero_of_eq v hv hij

lemma freeDifferentialDegree_relation (n : ℕ)
    (r : exteriorPower.presentation.Rels A (Fin n) (W K A)) :
    freeDifferentialDegree K A n (exteriorRelation K A n r) = 0 := by
  cases r with
  | add v i x y =>
    change freeDifferentialDegree K A n
      (Finsupp.single (Function.update v i x) 1 +
        Finsupp.single (Function.update v i y) 1 -
        Finsupp.single (Function.update v i (x + y)) 1) = 0
    simp only [map_sub, map_add, freeDifferentialDegree_single,
      Derivation.map_one_eq_zero, map_zero, zero_mul, one_smul,
      tupleDifferential_add_update]
    abel
  | smul v i a x =>
    change freeDifferentialDegree K A n
      (Finsupp.single (Function.update v i (a • x)) 1 -
        a • Finsupp.single (Function.update v i x) 1) = 0
    rw [map_sub, freeDifferentialDegree_smul]
    simp only [freeDifferentialDegree_single, presentationDegree_single,
      Derivation.map_one_eq_zero, map_zero, zero_mul, one_smul,
      tupleDifferential_smul_update]
    abel
  | alt v i j hv hij =>
    change freeDifferentialDegree K A n (Finsupp.single v 1) = 0
    simp only [freeDifferentialDegree_single, Derivation.map_one_eq_zero,
      map_zero, zero_mul, one_smul, tupleDifferential_eq_zero_of_eq K A n v i j hv hij,
      add_zero]

lemma freeDifferentialDegree_eq_zero_of_mem_relations (n : ℕ)
    {q : (Fin n → W K A) →₀ A}
    (hq : q ∈ Submodule.span A (Set.range (exteriorRelation K A n))) :
    freeDifferentialDegree K A n q = 0 := by
  classical
  have both : presentationDegree K A n q = 0 ∧ freeDifferentialDegree K A n q = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
    · rintro q ⟨r, rfl⟩
      constructor
      · rw [presentationDegree_eq_subtype_comp, LinearMap.comp_apply,
          presentationForms_relation, map_zero]
      · exact freeDifferentialDegree_relation K A n r
    · simp
    · intro q r hq hr iq ir
      constructor
      · rw [map_add, iq.1, ir.1, add_zero]
      · rw [map_add, iq.2, ir.2, add_zero]
    · intro a q hq iq
      constructor
      · rw [map_smul, iq.1, smul_zero]
      · rw [freeDifferentialDegree_smul, iq.1, mul_zero, iq.2, smul_zero, add_zero]
  exact both.2

/-- The `A`-span of the exterior-power presentation relations. -/
abbrev exteriorRelationsSpan (n : ℕ) :=
  Submodule.span A (Set.range (exteriorRelation K A n))

private lemma exteriorRelationsSpan_mkQ_relation (n : ℕ)
    (r : exteriorPower.presentation.Rels A (Fin n) (W K A)) :
    (exteriorRelationsSpan K A n).mkQ (exteriorRelation K A n r) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨r, rfl⟩)

private def exteriorRelationQuotientAlternating (n : ℕ) :
    (W K A) [⋀^Fin n]→ₗ[A] (((Fin n → W K A) →₀ A) ⧸ exteriorRelationsSpan K A n) where
  toFun v := (exteriorRelationsSpan K A n).mkQ (Finsupp.single v 1)
  map_update_add' v i x y := by
    have h := exteriorRelationsSpan_mkQ_relation K A n (.add v i x y)
    simp only [exteriorRelation, exteriorPower.presentation.relations_relation] at h
    have he (z : W K A) :
        @Function.update (Fin n) (fun _ => W K A) (instDecidableEqFin n) v i z =
          Function.update v i z := by
      funext j
      by_cases hj : j = i
      · subst j
        simp
      · simp only [Function.update_apply, ite_eq_right hj]
    rw [he x, he y, he (x + y)] at h
    rw [map_sub, map_add, sub_eq_zero] at h
    exact h.symm
  map_update_smul' v i a x := by
    have h := exteriorRelationsSpan_mkQ_relation K A n (.smul v i a x)
    simp only [exteriorRelation, exteriorPower.presentation.relations_relation] at h
    have he (z : W K A) :
        @Function.update (Fin n) (fun _ => W K A) (instDecidableEqFin n) v i z =
          Function.update v i z := by
      funext j
      by_cases hj : j = i
      · subst j
        simp
      · simp only [Function.update_apply, ite_eq_right hj]
    rw [he (a • x), he x] at h
    rw [map_sub, map_smul, sub_eq_zero] at h
    exact h
  map_eq_zero_of_eq' v i j hv hij :=
    exteriorRelationsSpan_mkQ_relation K A n (.alt v i j hv hij)

private def exteriorPresentationInverse (n : ℕ) :
    Forms K A n →ₗ[A] (((Fin n → W K A) →₀ A) ⧸ exteriorRelationsSpan K A n) :=
  exteriorPower.alternatingMapLinearEquiv (exteriorRelationQuotientAlternating K A n)

private lemma exteriorPresentationInverse_comp_projection (n : ℕ) :
    (exteriorPresentationInverse K A n).comp (presentationForms K A n) =
      (exteriorRelationsSpan K A n).mkQ := by
  ext v
  change exteriorPresentationInverse K A n
    (presentationForms K A n (Finsupp.single v 1)) =
    (exteriorRelationsSpan K A n).mkQ (Finsupp.single v 1)
  simp only [presentationForms, Finsupp.linearCombination_single, one_smul,
    exteriorPresentationInverse, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

lemma presentationForms_ker (n : ℕ) :
    (presentationForms K A n).ker = exteriorRelationsSpan K A n := by
  apply le_antisymm
  · intro q hq
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have h := LinearMap.congr_fun (exteriorPresentationInverse_comp_projection K A n) q
    rw [LinearMap.comp_apply, LinearMap.mem_ker.mp hq, map_zero] at h
    exact h.symm
  · rw [exteriorRelationsSpan, Submodule.span_le]
    rintro q ⟨r, rfl⟩
    exact presentationForms_relation K A n r

lemma presentationForms_surjective (n : ℕ) :
    Function.Surjective (presentationForms K A n) := by
  rw [← LinearMap.range_eq_top, presentationForms, Finsupp.range_linearCombination]
  exact exteriorPower.ιMulti_span A n (W K A)

lemma presentationForms_ker_restrict_le_differential_ker (n : ℕ) :
    ((presentationForms K A n).ker).restrictScalars K ≤
      (freeDifferentialDegree K A n).ker := by
  intro q hq
  apply freeDifferentialDegree_eq_zero_of_mem_relations K A n
  change q ∈ exteriorRelationsSpan K A n
  rw [← presentationForms_ker]
  exact hq

/-- The actual all-degree operator, descended over the base ring to the original exterior power. -/
def differentialToExterior (n : ℕ) : Forms K A n →ₗ[K] E K A :=
  ((((presentationForms K A n).ker).restrictScalars K).liftQ
      (freeDifferentialDegree K A n)
      (presentationForms_ker_restrict_le_differential_ker K A n)).comp
    ((Submodule.Quotient.restrictScalarsEquiv K (presentationForms K A n).ker).symm.toLinearMap.comp
      (((presentationForms K A n).quotKerEquivOfSurjective
        (presentationForms_surjective K A n)).symm.restrictScalars K).toLinearMap)

lemma differentialToExterior_presentation (n : ℕ) (q : (Fin n → W K A) →₀ A) :
    differentialToExterior K A n (presentationForms K A n q) =
      freeDifferentialDegree K A n q := by
  unfold differentialToExterior
  change (((presentationForms K A n).ker).restrictScalars K).liftQ
    (freeDifferentialDegree K A n) (presentationForms_ker_restrict_le_differential_ker K A n)
    ((Submodule.Quotient.restrictScalarsEquiv K (presentationForms K A n).ker).symm
      (((presentationForms K A n).quotKerEquivOfSurjective
        (presentationForms_surjective K A n)).symm (presentationForms K A n q))) = _
  have hq : ((presentationForms K A n).quotKerEquivOfSurjective
      (presentationForms_surjective K A n)).symm (presentationForms K A n q) =
      (presentationForms K A n).ker.mkQ q := by
    apply ((presentationForms K A n).quotKerEquivOfSurjective
      (presentationForms_surjective K A n)).injective
    simp
  rw [hq]
  rfl

private lemma forms_mul_mem {m n : ℕ} {x y : E K A}
    (hx : x ∈ Forms K A m) (hy : y ∈ Forms K A n) :
    x * y ∈ Forms K A (m + n) :=
  SetLike.mul_mem_graded hx hy

private lemma oneForm_mem (w : W K A) : ExteriorAlgebra.ι A w ∈ Forms K A 1 := by
  change ExteriorAlgebra.ι A w ∈ LinearMap.range (ExteriorAlgebra.ι A) ^ 1
  rw [Submodule.pow_one]
  exact LinearMap.mem_range_self _ w

private lemma orderedProduct_mem (ws : List (W K A)) :
    orderedProduct K A ws ∈ Forms K A ws.length := by
  have h := ExteriorAlgebra.ιMulti_range A ws.length ⟨ws.get, rfl⟩
  rw [← orderedProduct_ofFn] at h
  simpa only [List.ofFn_get, SetLike.mem_coe] using h

private lemma orderedDifferential_mem (ws : List (W K A)) :
    orderedDifferential K A ws ∈ Forms K A (ws.length + 1) := by
  induction ws with
  | nil =>
    rw [orderedDifferential_nil]
    exact Submodule.zero_mem _
  | cons w ws ih =>
    rw [orderedDifferential_cons]
    have h₁ := forms_mul_mem K A (differentialOneToExterior_mem_two K A w)
      (orderedProduct_mem K A ws)
    have h₂ := forms_mul_mem K A (oneForm_mem K A w) ih
    apply Submodule.sub_mem
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₁
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂

lemma tupleDifferential_mem (n : ℕ) (v : Fin n → W K A) :
    tupleDifferential K A n v ∈ Forms K A (n + 1) := by
  have h := orderedDifferential_mem K A (List.ofFn v)
  simpa only [List.length_ofFn, tupleDifferential] using h

lemma freeDifferentialDegree_mem (n : ℕ) (q : (Fin n → W K A) →₀ A) :
    freeDifferentialDegree K A n q ∈ Forms K A (n + 1) := by
  induction q using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add q r hq hr =>
    rw [map_add]
    exact Submodule.add_mem _ hq hr
  | single v a =>
    rw [freeDifferentialDegree_single]
    apply Submodule.add_mem
    · have h := forms_mul_mem K A (oneForm_mem K A (D K A a))
        (ExteriorAlgebra.ιMulti_range A n ⟨v, rfl⟩)
      simpa only [Nat.add_comm] using h
    · exact Submodule.smul_mem _ a (tupleDifferential_mem K A n v)

lemma differentialToExterior_mem (n : ℕ) (w : Forms K A n) :
    differentialToExterior K A n w ∈ Forms K A (n + 1) := by
  obtain ⟨q, rfl⟩ := presentationForms_surjective K A n w
  rw [differentialToExterior_presentation]
  exact freeDifferentialDegree_mem K A n q


lemma orderedDifferential_append (xs ys : List (W K A)) :
    orderedDifferential K A (xs ++ ys) =
      orderedDifferential K A xs * orderedProduct K A ys +
        (-1 : ℤˣ) ^ xs.length •
          (orderedProduct K A xs * orderedDifferential K A ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, orderedDifferential_cons,
      orderedProduct_cons, orderedProduct_append, ih]
    simp only [mul_add, sub_mul, mul_smul_comm, pow_succ, mul_smul,
      Units.neg_smul, one_smul, smul_neg, ← mul_assoc]
    abel

lemma tupleDifferential_append (m n : ℕ) (u : Fin m → W K A) (v : Fin n → W K A) :
    tupleDifferential K A (m + n) (Fin.append u v) =
      tupleDifferential K A m u * ExteriorAlgebra.ιMulti A n v +
        (-1 : ℤˣ) ^ m •
          (ExteriorAlgebra.ιMulti A m u * tupleDifferential K A n v) := by
  unfold tupleDifferential
  rw [List.ofFn_fin_append, orderedDifferential_append]
  simp only [List.length_ofFn, orderedProduct_ofFn]


/-- The original exterior-power projection on each weighted generator. -/
@[simp] theorem presentationForms_single (n : ℕ) (v : Fin n → W K A) (a : A) :
    presentationForms K A n (Finsupp.single v a) = a • exteriorPower.ιMulti A n v :=
  Finsupp.linearCombination_single _ _ _

lemma tupleDifferential_differentials (n : ℕ) (a : Fin n → A) :
    tupleDifferential K A n (fun i => D K A (a i)) = 0 := by
  have h := orderedDifferential_closed K A (List.ofFn a)
  simpa only [tupleDifferential, List.map_ofFn, Function.comp_def] using h

end KaehlerDifferential.DeRham
