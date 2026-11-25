/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.ClassicalDegreePresentation
public import MathlibExt.KTheory.Milnor.ClassicalSymbols

/-!
# Universal multilinear lifts in arbitrary Milnor degree

For a field `F`, an arbitrary-degree multilinear map on `Additive Fˣ`
first lifts to the degree-`n` component of the tensor ring through the
canonical tensor-power equivalence.  If this lift vanishes on the existing
set `TensorRing.steinbergInsertSet F n`, one span induction shows that it
kills the full degree-`n` Steinberg submodule and therefore descends to
`MilnorK F n` through the classical degree presentation.

The adjacent-slot predicate `IsAdjacentSteinberg` gives a degree-independent
criterion for this vanishing: every consecutive pair `a, 1-a` is killed.  A
single list-to-pure-tensor argument connects it to the existing insertion
generator set in every degree, including the vacuous degrees zero and one.

## Main definitions

* `degreeMultilinearLift`: the tensor-power lift on `TensorRing.degree F n`.
* `IsSteinbergInsertVanishing`: vanishing on every explicit degree-`n`
  Steinberg insertion.
* `IsAdjacentSteinberg`: vanishing whenever two adjacent tuple entries are a
  Steinberg pair.
* `liftDegree`: the descended map `MilnorK F n →ₗ[ℤ] A`.
* `liftDegreeOfAdjacentSteinberg`: the same descent from the adjacent
  Steinberg criterion.

## Main results

* `degreeMultilinearLift_tprod`, `liftDegree_mk`,
  `liftDegree_symbolMultilinear`, `liftDegree_symbolTuple`: computations on
  pure tensors and symbols.
* `IsAdjacentSteinberg.isSteinbergInsertVanishing`: the arbitrary-degree
  bridge from adjacent relations to the explicit insertion generators.
* `liftDegreeOfAdjacentSteinberg_mk`,
  `liftDegreeOfAdjacentSteinberg_symbolMultilinear`, and
  `liftDegreeOfAdjacentSteinberg_symbolTuple`: computations for the adjacent
  facade.
* `IsSteinbergInsertVanishing.le_ker_steinbergDegreeSpanInDegree`: the unique
  span induction used by the descent.
* `liftDegree_ext`, `liftDegree_congr`, and their adjacent-Steinberg versions:
  extensionality and congruence.
* `degreeMultilinearLift_compLinearMap`,
  `IsSteinbergInsertVanishing.compLinearMap`, `liftDegree_compLinearMap`, and
  their adjacent-Steinberg versions: functoriality under target-linear
  postcomposition.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open TensorAlgebra

namespace MilnorK

variable (F : Type*) [Field F]
variable {A : Type*} [AddCommGroup A] [Module ℤ A]

namespace TensorRing

/-- A tensor list obtained from a finite tuple is the corresponding pure
tensor in the tensor algebra. -/
theorem tensorList_ofFn_eq_tprod (n : ℕ) (f : Fin n → Fˣ) :
    tensorList F (List.ofFn f) =
      TensorAlgebra.tprod ℤ (Additive Fˣ) n (fun i => Additive.ofMul (f i)) := by
  rw [TensorAlgebra.tprod_apply]
  induction n with
  | zero => simp [List.ofFn_zero, tensorList_nil]
  | succ n ih => simp [List.ofFn_succ, tensorList_cons, List.prod_cons, ih]

end TensorRing

/-- The arbitrary-degree tensor-power lift of a multilinear map. -/
noncomputable def degreeMultilinearLift (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A) :
    TensorRing.degree F n →ₗ[ℤ] A :=
  (PiTensorProduct.lift β).comp
    (TensorAlgebra.degreeToTensorPower (R := ℤ) (M := Additive Fˣ) n)

/-- The tensor-power lift evaluates a pure degree-`n` tensor by the original
multilinear map. -/
@[simp]
theorem degreeMultilinearLift_tprod (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (v : Fin n → Additive Fˣ) :
    degreeMultilinearLift F n β
        (TensorAlgebra.toDegree (R := ℤ) (M := Additive Fˣ) n
          (PiTensorProduct.tprod ℤ v)) =
      β v := by
  unfold degreeMultilinearLift
  simp only [LinearMap.comp_apply]
  rw [TensorAlgebra.toDegree_tprod,
    TensorAlgebra.degreeToTensorPower_tprod,
    PiTensorProduct.lift.tprod]

/-- The degree lift vanishes on every explicit Steinberg insertion. -/
def IsSteinbergInsertVanishing (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A) : Prop :=
  ∀ (x : TensorRing.degree F n),
    (x : TensorRing F) ∈ TensorRing.steinbergInsertSet F n →
      degreeMultilinearLift F n β x = 0

/-- A degree-`n` multilinear map satisfies the adjacent Steinberg relation:
whenever entries `i` and `i+1` are `a` and `1-a`, the value is zero.  The
condition is vacuous in degrees zero and one. -/
def IsAdjacentSteinberg (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A) : Prop :=
  ∀ (v : Fin n → Additive Fˣ) (i : Fin n) (hi : i.val + 1 < n)
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1),
    v i = Additive.ofMul (Units.mk0 a ha0) →
    v ⟨i.val + 1, hi⟩ =
      Additive.ofMul (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) →
    β v = 0

/-- The adjacent Steinberg condition is vacuous in degree zero. -/
theorem isAdjacentSteinberg_zero
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 0 => Additive Fˣ) A) :
    IsAdjacentSteinberg F 0 β := by
  intro _ i
  exact Fin.elim0 i

/-- The adjacent Steinberg condition is vacuous in degree one. -/
theorem isAdjacentSteinberg_one
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin 1 => Additive Fˣ) A) :
    IsAdjacentSteinberg F 1 β := by
  intro _ i hi
  omega

/-- Adjacent Steinberg vanishing kills every generator in the explicit
degree-`n` Steinberg insertion set. -/
theorem IsAdjacentSteinberg.isSteinbergInsertVanishing
    {n : ℕ} {β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A}
    (hβ : IsAdjacentSteinberg F n β) :
    IsSteinbergInsertVanishing F n β := by
  rintro ⟨x, hxDeg⟩ ⟨xs, ys, a, ha0, ha1, hlen, rfl⟩
  let a0 : Fˣ := Units.mk0 a ha0
  let a1 : Fˣ := Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)
  let zs : List Fˣ := xs ++ [a0, a1] ++ ys
  have hzsLen : zs.length = n := by
    simp only [zs, List.length_append, List.length_cons, List.length_nil]
    omega
  let u : Fin n → Fˣ := fun i =>
    zs[i.val]'(by rw [hzsLen]; exact i.isLt)
  let v : Fin n → Additive Fˣ := fun i => Additive.ofMul (u i)
  have hofFn : List.ofFn u = zs := by
    apply List.ext_getElem
    · simp [hzsLen]
    · intro i hi hi'
      simp [u]
  have hword :
      TensorRing.tensorList F xs *
          (TensorAlgebra.ι ℤ (Additive.ofMul a0) *
            TensorAlgebra.ι ℤ (Additive.ofMul a1)) *
          TensorRing.tensorList F ys =
        TensorRing.tensorList F zs := by
    simp [zs, TensorRing.tensorList_append, mul_assoc]
  have hi0 : xs.length < n := by omega
  let i : Fin n := ⟨xs.length, hi0⟩
  have hiSucc : i.val + 1 < n := by
    dsimp [i]
    omega
  have hv0 : v i = Additive.ofMul a0 := by
    simp [v, u, i, zs]
  have hv1 : v ⟨i.val + 1, hiSucc⟩ = Additive.ofMul a1 := by
    simp [v, u, i, zs]
  have hpure :
      (⟨TensorRing.tensorList F xs *
          (TensorAlgebra.ι ℤ (Additive.ofMul a0) *
            TensorAlgebra.ι ℤ (Additive.ofMul a1)) *
          TensorRing.tensorList F ys, hxDeg⟩ : TensorRing.degree F n) =
        TensorAlgebra.toDegree (R := ℤ) (M := Additive Fˣ) n
          (PiTensorProduct.tprod ℤ v) := by
    apply Subtype.ext
    rw [TensorAlgebra.toDegree_tprod]
    calc
      TensorRing.tensorList F xs *
            (TensorAlgebra.ι ℤ (Additive.ofMul a0) *
              TensorAlgebra.ι ℤ (Additive.ofMul a1)) *
            TensorRing.tensorList F ys =
          TensorRing.tensorList F zs := hword
      _ = TensorRing.tensorList F (List.ofFn u) := by rw [hofFn]
      _ = TensorAlgebra.tprod ℤ (Additive Fˣ) n v := by
        simpa [v] using TensorRing.tensorList_ofFn_eq_tprod F n u
  change degreeMultilinearLift F n β
      ⟨TensorRing.tensorList F xs *
          (TensorAlgebra.ι ℤ (Additive.ofMul a0) *
            TensorAlgebra.ι ℤ (Additive.ofMul a1)) *
          TensorRing.tensorList F ys, hxDeg⟩ = 0
  rw [hpure, degreeMultilinearLift_tprod]
  exact hβ v i hiSucc a ha0 ha1 hv0 hv1

/-- Vanishing on the explicit Steinberg generators implies vanishing on their
full span in the degree component.  This is the single span induction in the
generic descent. -/
theorem IsSteinbergInsertVanishing.le_ker_steinbergDegreeSpanInDegree
    {n : ℕ} {β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A}
    (hβ : IsSteinbergInsertVanishing F n β) :
    steinbergDegreeSpanInDegree F n ≤
      LinearMap.ker (degreeMultilinearLift F n β) := by
  intro x hx
  rw [LinearMap.mem_ker]
  have hval : x.val ∈ TensorRing.steinbergDegreeSpan F n := by
    dsimp [steinbergDegreeSpanInDegree] at hx
    rwa [Submodule.mem_comap] at hx
  have hv : ∀ {y : TensorRing F}
      (hy : y ∈ TensorRing.steinbergDegreeSpan F n)
      (hyDeg : y ∈ TensorRing.degree F n),
      degreeMultilinearLift F n β ⟨y, hyDeg⟩ = 0 := by
    intro y hy hyDeg
    induction hy using Submodule.span_induction with
    | mem z hz =>
        exact hβ ⟨z, hyDeg⟩ hz
    | zero =>
        have heq : (⟨(0 : TensorRing F), hyDeg⟩ :
            TensorRing.degree F n) = 0 := by
          apply Subtype.ext
          simp
        rw [heq, map_zero]
    | add y z hy hz ihy ihz =>
        have hyDeg' : y ∈ TensorRing.degree F n :=
          TensorRing.steinbergDegreeSpan_le_degree F n hy
        have hzDeg' : z ∈ TensorRing.degree F n :=
          TensorRing.steinbergDegreeSpan_le_degree F n hz
        have heq : (⟨y + z, hyDeg⟩ : TensorRing.degree F n) =
            ⟨y, hyDeg'⟩ + ⟨z, hzDeg'⟩ := by
          apply Subtype.ext
          simp
        rw [heq, map_add, ihy hyDeg', ihz hzDeg', add_zero]
    | smul c y hy ihy =>
        have hyDeg' : y ∈ TensorRing.degree F n :=
          TensorRing.steinbergDegreeSpan_le_degree F n hy
        have heq : (⟨c • y, hyDeg⟩ : TensorRing.degree F n) =
            c • ⟨y, hyDeg'⟩ := by
          apply Subtype.ext
          simp
        rw [heq, LinearMap.map_smul, ihy hyDeg', smul_zero]
  exact hv hval x.2

/-- The arbitrary-degree Milnor lift obtained by quotienting the tensor lift
by the degree-`n` Steinberg span. -/
noncomputable def liftDegree (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsSteinbergInsertVanishing F n β) :
    MilnorK F n →ₗ[ℤ] A :=
  ((steinbergDegreeSpanInDegree F n).liftQ (degreeMultilinearLift F n β)
      hβ.le_ker_steinbergDegreeSpanInDegree).comp
    (classicalPresentationEquiv F n).toLinearMap

/-- The arbitrary-degree Milnor lift obtained from adjacent Steinberg
vanishing. -/
noncomputable def liftDegreeOfAdjacentSteinberg (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsAdjacentSteinberg F n β) :
    MilnorK F n →ₗ[ℤ] A :=
  liftDegree F n β hβ.isSteinbergInsertVanishing

/-- Computation of the descended lift on a class represented by a degree
tensor. -/
@[simp]
theorem liftDegree_mk (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsSteinbergInsertVanishing F n β)
    (x : TensorRing.degree F n) :
    liftDegree F n β hβ (mk F n x) = degreeMultilinearLift F n β x := by
  simp [liftDegree, classicalPresentationEquiv_apply_mk,
    Submodule.liftQ_apply]

/-- Computation of the adjacent-Steinberg lift on a class represented by a
degree tensor. -/
@[simp]
theorem liftDegreeOfAdjacentSteinberg_mk (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsAdjacentSteinberg F n β) (x : TensorRing.degree F n) :
    liftDegreeOfAdjacentSteinberg F n β hβ (mk F n x) =
      degreeMultilinearLift F n β x :=
  liftDegree_mk F n β hβ.isSteinbergInsertVanishing x

/-- Computation of the descended lift on the canonical multilinear Milnor
symbol. -/
@[simp]
theorem liftDegree_symbolMultilinear (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsSteinbergInsertVanishing F n β)
    (v : Fin n → Additive Fˣ) :
    liftDegree F n β hβ (symbolMultilinear F n v) = β v := by
  change liftDegree F n β hβ
      (mk F n (TensorAlgebra.toDegree (R := ℤ) (M := Additive Fˣ) n
        (PiTensorProduct.tprod ℤ v))) = β v
  rw [liftDegree_mk, degreeMultilinearLift_tprod]

/-- Computation of the adjacent-Steinberg lift on a multilinear symbol. -/
@[simp]
theorem liftDegreeOfAdjacentSteinberg_symbolMultilinear (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsAdjacentSteinberg F n β) (v : Fin n → Additive Fˣ) :
    liftDegreeOfAdjacentSteinberg F n β hβ
        (symbolMultilinear F n v) = β v :=
  liftDegree_symbolMultilinear F n β hβ.isSteinbergInsertVanishing v

/-- Computation of the descended lift on a tuple of field units. -/
@[simp]
theorem liftDegree_symbolTuple (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsSteinbergInsertVanishing F n β)
    (v : Fin n → Fˣ) :
    liftDegree F n β hβ (symbolTuple F n v) =
      β (fun i => Additive.ofMul (v i)) := by
  rw [← symbolMultilinear_apply, liftDegree_symbolMultilinear]

/-- Computation of the adjacent-Steinberg lift on a tuple of field units. -/
@[simp]
theorem liftDegreeOfAdjacentSteinberg_symbolTuple (n : ℕ)
    (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsAdjacentSteinberg F n β) (v : Fin n → Fˣ) :
    liftDegreeOfAdjacentSteinberg F n β hβ (symbolTuple F n v) =
      β (fun i => Additive.ofMul (v i)) :=
  liftDegree_symbolTuple F n β hβ.isSteinbergInsertVanishing v

/-- Two arbitrary-degree lifts agreeing on pure tuples of units are equal. -/
theorem liftDegree_ext (n : ℕ)
    (β₁ β₂ : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (h₁ : IsSteinbergInsertVanishing F n β₁)
    (h₂ : IsSteinbergInsertVanishing F n β₂)
    (h : ∀ v : Fin n → Fˣ,
      β₁ (fun i => Additive.ofMul (v i)) =
        β₂ (fun i => Additive.ofMul (v i))) :
    liftDegree F n β₁ h₁ = liftDegree F n β₂ h₂ := by
  apply symbolTuple_ext F
  intro v
  rw [liftDegree_symbolTuple, liftDegree_symbolTuple, h]

/-- Adjacent-Steinberg lifts agreeing on pure tuples of units are equal. -/
theorem liftDegreeOfAdjacentSteinberg_ext (n : ℕ)
    (β₁ β₂ : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (h₁ : IsAdjacentSteinberg F n β₁)
    (h₂ : IsAdjacentSteinberg F n β₂)
    (h : ∀ v : Fin n → Fˣ,
      β₁ (fun i => Additive.ofMul (v i)) =
        β₂ (fun i => Additive.ofMul (v i))) :
    liftDegreeOfAdjacentSteinberg F n β₁ h₁ =
      liftDegreeOfAdjacentSteinberg F n β₂ h₂ :=
  liftDegree_ext F n β₁ β₂ h₁.isSteinbergInsertVanishing
    h₂.isSteinbergInsertVanishing h

/-- Congruent multilinear maps have equal descended lifts. -/
theorem liftDegree_congr (n : ℕ)
    (β₁ β₂ : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (h₁ : IsSteinbergInsertVanishing F n β₁)
    (h₂ : IsSteinbergInsertVanishing F n β₂)
    (h : β₁ = β₂) :
    liftDegree F n β₁ h₁ = liftDegree F n β₂ h₂ := by
  subst h
  rfl

/-- Congruent multilinear maps have equal adjacent-Steinberg lifts. -/
theorem liftDegreeOfAdjacentSteinberg_congr (n : ℕ)
    (β₁ β₂ : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (h₁ : IsAdjacentSteinberg F n β₁)
    (h₂ : IsAdjacentSteinberg F n β₂) (h : β₁ = β₂) :
    liftDegreeOfAdjacentSteinberg F n β₁ h₁ =
      liftDegreeOfAdjacentSteinberg F n β₂ h₂ := by
  subst h
  rfl

/-- The tensor-power lift commutes with target-linear postcomposition. -/
theorem degreeMultilinearLift_compLinearMap
    {B : Type*} [AddCommGroup B] [Module ℤ B]
    (n : ℕ) (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (f : A →ₗ[ℤ] B) :
    degreeMultilinearLift F n (f.compMultilinearMap β) =
      f.comp (degreeMultilinearLift F n β) := by
  have hLift : f.comp (PiTensorProduct.lift β) =
      PiTensorProduct.lift (f.compMultilinearMap β) := by
    apply PiTensorProduct.lift.unique
    intro v
    simp only [LinearMap.comp_apply, PiTensorProduct.lift.tprod,
      LinearMap.compMultilinearMap_apply]
  apply LinearMap.ext
  intro x
  change PiTensorProduct.lift (f.compMultilinearMap β)
      (TensorAlgebra.degreeToTensorPower
        (R := ℤ) (M := Additive Fˣ) n x) =
    f (PiTensorProduct.lift β
      (TensorAlgebra.degreeToTensorPower
        (R := ℤ) (M := Additive Fˣ) n x))
  exact (DFunLike.congr_fun hLift _).symm

/-- Vanishing on Steinberg insertions is preserved by target-linear
postcomposition. -/
theorem IsSteinbergInsertVanishing.compLinearMap
    {B : Type*} [AddCommGroup B] [Module ℤ B]
    {n : ℕ} {β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A}
    (hβ : IsSteinbergInsertVanishing F n β) (f : A →ₗ[ℤ] B) :
    IsSteinbergInsertVanishing F n (f.compMultilinearMap β) := by
  intro x hx
  rw [degreeMultilinearLift_compLinearMap, LinearMap.comp_apply,
    hβ x hx, map_zero]

/-- Adjacent Steinberg vanishing is preserved by target-linear
postcomposition. -/
theorem IsAdjacentSteinberg.compLinearMap
    {B : Type*} [AddCommGroup B] [Module ℤ B]
    {n : ℕ} {β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A}
    (hβ : IsAdjacentSteinberg F n β) (f : A →ₗ[ℤ] B) :
    IsAdjacentSteinberg F n (f.compMultilinearMap β) := by
  intro v i hi a ha0 ha1 hv0 hv1
  rw [LinearMap.compMultilinearMap_apply,
    hβ v i hi a ha0 ha1 hv0 hv1, map_zero]

/-- Descending and target-linear postcomposition commute. -/
theorem liftDegree_compLinearMap
    {B : Type*} [AddCommGroup B] [Module ℤ B]
    (n : ℕ) (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsSteinbergInsertVanishing F n β) (f : A →ₗ[ℤ] B) :
    liftDegree F n (f.compMultilinearMap β)
        (IsSteinbergInsertVanishing.compLinearMap F hβ f) =
      f.comp (liftDegree F n β hβ) := by
  apply symbolTuple_ext F
  intro v
  simp only [liftDegree_symbolTuple, LinearMap.comp_apply,
    LinearMap.compMultilinearMap_apply]

/-- Adjacent-Steinberg descent commutes with target-linear
postcomposition. -/
theorem liftDegreeOfAdjacentSteinberg_compLinearMap
    {B : Type*} [AddCommGroup B] [Module ℤ B]
    (n : ℕ) (β : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) A)
    (hβ : IsAdjacentSteinberg F n β) (f : A →ₗ[ℤ] B) :
    liftDegreeOfAdjacentSteinberg F n (f.compMultilinearMap β)
        (IsAdjacentSteinberg.compLinearMap F hβ f) =
      f.comp (liftDegreeOfAdjacentSteinberg F n β hβ) := by
  exact liftDegree_compLinearMap F n β
    hβ.isSteinbergInsertVanishing f

end MilnorK
