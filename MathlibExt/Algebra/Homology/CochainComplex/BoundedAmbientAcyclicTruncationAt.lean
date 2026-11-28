/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicTopKernel
public import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
public import MathlibExt.Algebra.Homology.HomotopyCofiberQuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexKernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Single

/-!
# Upper kernel truncation at an explicit support interval

Let E be preadditive with a zero object and binary biproducts, and let K
have a supplied term-support interval [a,b].
The top disk is the identity cofiber on the single object K^b.
The chain projection uses the degree-zero top-term cochain and its negative
boundary; its lower differential component is positive and its upper
component is the canonical identity chart.

With a Quillen exact structure on E and a fully faithful additive ambient
embedding F, essential-image closure
under kernels of epimorphisms and reflection of admissible exactness,
ambient acyclicity makes the projection degreewise admissible epic.
Its kernel has support [a,b−1]. For exact F the kernel remains ambient
acyclic and its cofiber descendant to the disk is an ambient
quasi-isomorphism. The supplied support endpoints remain fixed
throughout the construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CochainComplex.HomComplex
open scoped ZeroObject

namespace CochainComplex.Bounded.TruncationAt

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E]

variable (b : ℤ)

omit [HasZeroObject E] [HasBinaryBiproducts E] in
/-- Let E be preadditive and K a bounded integer cochain complex.
If K^j is zero for j<a or b<j and b<a, then the underlying cochain
complex K is a zero object. -/
theorem isZero_of_empty_window (K : Bounded E) (a : ℤ)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (hEmpty : b < a) :
    IsZero K.obj := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext j
  exact (hSupport j (by omega)).eq_of_tgt _ _

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The top single complex S_t has K^t in degree t and zero terms elsewhere. -/
abbrev topDiskSingle (K : Bounded E) : CochainComplex E ℤ :=
  (HomologicalComplex.single E (.up ℤ) (b)).obj (K.obj.X (b))

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The raw top disk is the homotopy cofiber D_t of the identity of S_t. -/
abbrev topDiskRaw (K : Bounded E) : CochainComplex E ℤ :=
  HomologicalComplex.homotopyCofiber (𝟙 (topDiskSingle (b := b) K))

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The disk term D_t^j is zero for j≠t−1 and j≠t. -/
theorem topDisk_isZero_X (K : Bounded E) (j : ℤ)
    (hLower : j ≠ b - 1) (hUpper : j ≠ b) :
    IsZero ((topDiskRaw (b := b) K).X j) := by
  apply HomologicalComplex.homotopyCofiber.isZero_X (𝟙 (topDiskSingle (b := b) K)) j
  · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) (b)
      (K.obj.X (b)) j hUpper
  · intro k hk
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) (b)
      (K.obj.X (b)) k (by change j + 1 = k at hk; omega)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The canonical lower chart ℓ identifies K^t with D_t^{t−1}. -/
def topDiskLowerIso (K : Bounded E) :
    K.obj.X (b) ≅ (topDiskRaw (b := b) K).X (b - 1) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
    (K.obj.X (b))).symm ≪≫
      isoBiprodZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) (b)
        (K.obj.X (b)) (b - 1) (by omega)) ≪≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 (topDiskSingle (b := b) K))
        (b - 1) (b)
        (ComplexShape.up_mk _ _ (by omega))).symm

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The canonical upper chart u identifies K^t with D_t^t. -/
def topDiskUpperIso (K : Bounded E) :
    K.obj.X (b) ≅ (topDiskRaw (b := b) K).X (b) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
    (K.obj.X (b))).symm ≪≫
      isoZeroBiprod (HomologicalComplex.isZero_single_obj_X (.up ℤ) (b)
        (K.obj.X (b)) (b + 1) (by omega)) ≪≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 (topDiskSingle (b := b) K))
        (b) (b + 1) (ComplexShape.up_mk _ _ rfl)).symm

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The lower chart is the single-term identification followed by the shifted-source cofiber inclusion.
-/
theorem topDiskLowerIso_hom (K : Bounded E) :
    (topDiskLowerIso (b := b) K).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
        (K.obj.X (b))).inv ≫
      HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K))
        (b) (b - 1)
        (ComplexShape.up_mk _ _ (by omega)) := rfl

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The upper chart is the single-term identification followed by the target cofiber inclusion. -/
theorem topDiskUpperIso_hom (K : Bounded E) :
    (topDiskUpperIso (b := b) K).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
        (K.obj.X (b))).inv ≫
      HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle (b := b) K)) (b) := by
  exact congrArg
    (fun f => (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
      (K.obj.X (b))).inv ≫ f)
    (HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv (𝟙 (topDiskSingle (b := b) K))
      (b + 1) (b) (ComplexShape.up_mk _ _ rfl))

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The disk differential satisfies d_D^{t−1}∘ℓ=u, so it is positive identity in these two charts. -/
theorem topDiskLowerIso_hom_d (K : Bounded E) :
    (topDiskLowerIso (b := b) K).hom ≫ (topDiskRaw (b := b) K).d (b - 1) (b) =
      (topDiskUpperIso (b := b) K).hom := by
  have hd := HomologicalComplex.homotopyCofiber.inlX_d (𝟙 (topDiskSingle (b := b) K))
    (b - 1) (b) (b + 1)
    (ComplexShape.up_mk _ _ (by omega)) (ComplexShape.up_mk _ _ rfl)
  have hpos : HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K))
      (b) (b - 1) (ComplexShape.up_mk _ _ (by omega)) ≫
      (topDiskRaw (b := b) K).d (b - 1) (b) =
      HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle (b := b) K)) (b) := by
    change HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K))
      (b) (b - 1) (ComplexShape.up_mk _ _ (by omega)) ≫
      HomologicalComplex.homotopyCofiber.d (𝟙 (topDiskSingle (b := b) K))
        (b - 1) (b) = _
    simpa only [topDiskSingle, HomologicalComplex.single_obj_d, neg_zero, zero_comp,
      HomologicalComplex.id_f, Category.id_comp, zero_add] using hd
  rw [topDiskLowerIso_hom (b := b), topDiskUpperIso_hom (b := b), Category.assoc]
  exact congrArg (fun f =>
    (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
      (K.obj.X (b))).inv ≫ f) hpos

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The degree-zero cochain f₀:K → S_t is identity in the top term and zero in other degrees. -/
def topDiskCochain (K : Bounded E) : Cochain K.obj (topDiskSingle (b := b) K) 0 :=
  Cochain.ofHoms (fun j => if h : j = b then
    eqToHom (congrArg K.obj.X h) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
        (K.obj.X (b))).inv ≫
      eqToHom (congrArg (topDiskSingle (b := b) K).X h.symm) else 0)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The degree-one cocycle h=−∂f₀, the negative Hom-complex boundary of the top-term cochain, supplies
the shifted-source cone coordinate. -/
def topDiskBoundary (K : Bounded E) : Cocycle K.obj (topDiskSingle (b := b) K) 1 :=
  Cocycle.mk (-δ 0 1 (topDiskCochain (b := b) K)) 2 rfl (by simp only [δ_neg, δ_δ, neg_zero])

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The chain map π:K → D_t is the cone lift formed from f₀ and h=−∂f₀. -/
def topDiskProjection (K : Bounded E) : K.obj ⟶ topDiskRaw (b := b) K :=
  mappingCone.lift (𝟙 (topDiskSingle (b := b) K)) (topDiskBoundary (b := b) K) (topDiskCochain (b
    := b) K) (by
    simp only [topDiskBoundary, Cocycle.mk, Cochain.comp_id]
    exact add_neg_cancel _)

omit [HasBinaryBiproducts E] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The top component of f₀ is the inverse single-term identification K^t → S_t^t. -/
theorem topDiskCochain_self (K : Bounded E) :
    (topDiskCochain (b := b) K).v (b) (b) (add_zero _) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (b)
        (K.obj.X (b))).inv := by
  simp only [topDiskCochain, Cochain.ofHoms_v, dite_eq_left rfl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

omit [HasBinaryBiproducts E] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The component of f₀ is zero in every degree j≠t. -/
theorem topDiskCochain_ne (K : Bounded E) (j : ℤ) (hj : j ≠ b) :
    (topDiskCochain (b := b) K).v j j (add_zero _) = 0 := by
  simp only [topDiskCochain, Cochain.ofHoms_v, dite_eq_right hj]

omit [HasBinaryBiproducts E] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

For p+1=q, the negative boundary has component h_{p,q}=f₀,q∘d_K(p,q), with positive differential
sign. -/
theorem topDiskBoundary_v (K : Bounded E) (p q : ℤ) (hpq : p + 1 = q) :
    (topDiskBoundary (b := b) K).1.v p q hpq =
      K.obj.d p q ≫ (topDiskCochain (b := b) K).v q q (add_zero _) := by
  change (-δ 0 1 (topDiskCochain (b := b) K)).v p q hpq = _
  rw [Cochain.neg_v, δ_v 0 1 rfl (topDiskCochain (b := b) K) p q hpq p q (by omega) hpq]
  simp only [topDiskSingle, HomologicalComplex.single_obj_d, comp_zero,
    Int.negOnePow_one, Units.neg_smul, one_smul, zero_add, neg_neg]

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

In degree j the projection π_j is the sum of h_{j,j+1} followed by the shifted-source inclusion and
f₀,j followed by the target inclusion. -/
theorem topDiskProjection_f (K : Bounded E) (j : ℤ) :
    (topDiskProjection (b := b) K).f j =
      (topDiskBoundary (b := b) K).1.v j (j + 1) rfl ≫
          HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K)) (j + 1) j rfl +
        (topDiskCochain (b := b) K).v j j (add_zero j) ≫
          HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle (b := b) K)) j :=
  mappingCone.lift_f _ _ _ _ j (j + 1) rfl

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

For p+1=q, the projection π_p equals the shifted-source inclusion composed with h_{p,q}, plus the
target inclusion composed with f₀,p. -/
theorem topDiskProjection_f' (K : Bounded E) (p q : ℤ) (hpq : p + 1 = q) :
    (topDiskProjection (b := b) K).f p =
      (topDiskBoundary (b := b) K).1.v p q hpq ≫
          HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle (b := b) K)) q p
            (ComplexShape.up_mk _ _ hpq) +
        (topDiskCochain (b := b) K).v p p (add_zero p) ≫
          HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle (b := b) K)) p :=
  mappingCone.lift_f _ _ _ _ p q hpq

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The upper projection component π_t equals the upper chart u. -/
theorem topDiskProjection_f_upper (K : Bounded E) :
    (topDiskProjection (b := b) K).f (b) = (topDiskUpperIso (b := b) K).hom := by
  rw [topDiskProjection_f' (b := b) K (b) (b + 1) rfl,
    topDiskBoundary_v (b := b), topDiskCochain_ne (b := b) K (b + 1) (by omega),
    comp_zero, zero_comp, zero_add, topDiskCochain_self (b := b)]
  exact (topDiskUpperIso_hom (b := b) K).symm

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The lower component is π_{t−1}=ℓ∘d_K^{t−1}, with positive sign. -/
theorem topDiskProjection_f_lower (K : Bounded E) :
    (topDiskProjection (b := b) K).f (b - 1) =
      K.obj.d (b - 1) (b) ≫ (topDiskLowerIso (b := b) K).hom := by
  rw [topDiskProjection_f' (b := b) K (b - 1) (b) (by omega),
    topDiskBoundary_v (b := b), topDiskCochain_self (b := b),
    topDiskCochain_ne (b := b) K (b - 1) (by omega), zero_comp, add_zero,
    topDiskLowerIso_hom (b := b), Category.assoc]

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The upper projection component π_t is an isomorphism. -/
theorem topDiskProjection_isIso_upper (K : Bounded E) :
    IsIso ((topDiskProjection (b := b) K).f (b)) := by
  rw [topDiskProjection_f_upper (b := b)]
  infer_instance

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The raw disk has finite support [t−1,t] and is bounded. -/
theorem bounded_topDiskRaw (K : Bounded E) : CochainComplex.bounded E (topDiskRaw (b := b) K) := by
  refine ⟨b - 1, b, ?_⟩
  intro j hj
  exact topDisk_isZero_X (b := b) K j (by omega) (by omega)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The identity cofiber D_t, with its support [t−1,t], is an object of the bounded cochain category. -/
def topDisk (K : Bounded E) : Bounded E := ⟨topDiskRaw (b := b) K, bounded_topDiskRaw (b := b) K⟩

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The projection π:K → D_t is the corresponding morphism of bounded complexes. -/
def topDiskProjectionBounded (K : Bounded E) : K ⟶ topDisk (b := b) K :=
  ObjectProperty.homMk (topDiskProjection (b := b) K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

Forgetting boundedness from the bounded projection gives the original chain map π:K → D_t. -/
theorem topDiskProjectionBounded_hom (K : Bounded E) :
    (topDiskProjectionBounded (b := b) K).hom = topDiskProjection (b := b) K := rfl

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The top disk admits the canonical homotopy from its identity to zero, as the cofiber of an identity
map. -/
def topDiskContraction (K : Bounded E) :
    _root_.Homotopy (𝟙 (topDiskRaw (b := b) K)) 0 := by
  change _root_.Homotopy (𝟙 (mappingCone (𝟙 (topDiskSingle (b := b) K)))) 0
  exact mappingCone.descHomotopy (𝟙 (topDiskSingle (b := b) K))
    (𝟙 (mappingCone (𝟙 (topDiskSingle (b := b) K)))) 0
    0 (mappingCone.inl (𝟙 (topDiskSingle (b := b) K))) (by simp) (by simp)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Let F:E → A be any additive functor
with A abelian.

The ambient image F(D_t) is acyclic. -/
theorem topDisk_map_acyclic {A : Type uA} [Category.{vA} A] [Abelian A]
    (F : E ⥤ A) [F.Additive] (K : Bounded E) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (topDiskRaw (b := b) K)).Acyclic := by
  let M := (F.mapHomologicalComplex (.up ℤ)).obj (topDiskRaw (b := b) K)
  have hContract : _root_.Homotopy (𝟙 M) 0 := by
    have hid : (F.mapHomologicalComplex (.up ℤ)).map (𝟙 (topDiskRaw (b := b) K)) = 𝟙 M :=
      (F.mapHomologicalComplex (.up ℤ)).map_id _
    have hz : (F.mapHomologicalComplex (.up ℤ)).map (0 : topDiskRaw (b := b) K ⟶ topDiskRaw (b :=
      b) K) = 0 :=
      (F.mapHomologicalComplex (.up ℤ)).map_zero _ _
    have h := F.mapHomotopy (topDiskContraction (b := b) K)
    rw [hid, hz] at h
    exact h
  intro j
  apply (M.exactAt_iff_isZero_homology j).mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero]
    using hContract.homologyMap_eq j

variable [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

include hKernelClosure

variable (a : ℤ)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Every component π_j is an admissible epimorphism in E. -/
theorem topDiskProjection_isAdmissibleEpi (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleEpi ((topDiskProjection (b := b) K).f j) := by
  by_cases hUpper : j = b
  · subst j
    let _ := topDiskProjection_isIso_upper (b := b) K
    exact isAdmissibleEpi_of_isIso _
  by_cases hLower : j = b - 1
  · subst j
    rw [topDiskProjection_f_lower (b := b)]
    let _ : Epi (F.map (K.obj.d (b - 1) b)) :=
      mappedDifferential_epi_of_acyclic_of_isZero_succ F K b
        (hSupport (b + 1) (Or.inr (by omega))) hK
    have hAdmissible : IsAdmissibleEpi (K.obj.d (b - 1) b) :=
      isAdmissibleEpi_g (F.kernelLiftOfEpi_isAdmissibleExact hKernelClosure (K.obj.d (b - 1) b))
    exact admissibleEpi_comp.comp_mem _ _ hAdmissible
      (isAdmissibleEpi_of_isIso (topDiskLowerIso (b := b) K).hom)
  let e := (topDisk_isZero_X (b := b) K j hLower hUpper).iso (isZero_zero E)
  have hComp : IsAdmissibleEpi
      (((topDiskProjection (b := b) K).f j ≫ e.hom) ≫ e.inv) :=
    admissibleEpi_comp.comp_mem _ _ (IsAdmissibleEpi.toZero _)
      (isAdmissibleEpi_of_isIso e.inv)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hComp

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

For every degree j, the kernel of the component π_j exists in E. -/
theorem topDiskProjection_hasKernel_f (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    HasKernel ((topDiskProjection (b := b) K).f j) := by
  obtain ⟨Z, i, w, hS⟩ := topDiskProjection_isAdmissibleEpi (b := b) (a := a) (hSupport :=
    hSupport) F hKernelClosure K hK j
  exact ⟨⟨⟨KernelFork.ofι i w, isLimit_kernelFork_of_isAdmissibleExact hS⟩⟩⟩

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The kernel of π exists in the category of integer cochain complexes, computed from its component
kernels. -/
theorem topDiskProjection_hasKernel (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    HasKernel (topDiskProjection (b := b) K) := by
  let _ : ∀ j, HasKernel ((topDiskProjection (b := b) K).f j) :=
    topDiskProjection_hasKernel_f (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK
  exact HomologicalComplex.hasKernel_of_hasKernel_f _

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw upper truncation is T=Ker(π), with its cochain differential induced from K. -/
def topTruncationRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : CochainComplex E ℤ := by
  let _ := topDiskProjection_hasKernel (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK
  exact kernel (topDiskProjection (b := b) K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw truncation inclusion is the cochain kernel map i:T → K. -/
def topTruncationRawι (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ⟶ K.obj := by
  let _ := topDiskProjection_hasKernel (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK
  exact kernel.ι (topDiskProjection (b := b) K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The projection kills the kernel inclusion: π∘i=0. -/
theorem topTruncationRawι_projection (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ≫
      topDiskProjection (b := b) K = 0 := by
  let _ := topDiskProjection_hasKernel (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK
  exact kernel.condition _

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The inclusion i:T → K is a kernel of π in the cochain category. -/
def topTruncationKernelIsLimit (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsLimit (KernelFork.ofι (f := topDiskProjection (b := b) K)
      (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK)
      (topTruncationRawι_projection (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK)) := by
  let _ := topDiskProjection_hasKernel (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK
  exact kernelIsKernel _

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

In every degree j, i_j:T^j → K^j is a kernel of π_j. -/
def topTruncationTermIsLimit (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsLimit (KernelFork.ofι (f := (topDiskProjection (b := b) K).f j)
      ((topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).f j) (by
        exact congrArg (fun t => t.f j) (topTruncationRawι_projection (b := b) (a := a) (hSupport
          := hSupport) F hKernelClosure K hK))) := by
  let _ : ∀ n, HasKernel ((topDiskProjection (b := b) K).f n) :=
    topDiskProjection_hasKernel_f (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK
  let _ := HomologicalComplex.eval_preservesLimit_of_hasKernel_f (topDiskProjection (b := b) K) j
  exact KernelFork.mapIsLimit _ (topTruncationKernelIsLimit (b := b) (a := a) (hSupport :=
    hSupport) F hKernelClosure K hK)
    (HomologicalComplex.eval E (.up ℤ) j)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

If K^j is zero, the kernel term T^j is zero. -/
theorem topTruncationRaw_isZero_X_of_isZero (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ)
    (hj : IsZero (K.obj.X j)) :
    IsZero ((topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).X j)
      := by
  let _ : Mono ((topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK).f j) :=
    Fork.IsLimit.mono (topTruncationTermIsLimit (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK j)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono ((topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK).f j)).mp
  simp only [Category.id_comp, zero_comp]
  exact hj.eq_of_tgt _ _

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The upper kernel term T^t is zero because π_t is invertible. -/
theorem topTruncationRaw_isZero_X_upper (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsZero ((topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).X
      (b)) := by
  let _ := topDiskProjection_isIso_upper (b := b) K
  exact KernelFork.IsLimit.isZero_of_mono
    (topTruncationTermIsLimit (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK (b))

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The kernel truncation has support [a,t−1]. -/
theorem topTruncationRaw_support (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ∀ j : ℤ, j < a ∨ b - 1 < j →
      IsZero ((topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).X
        j) := by
  intro j hj
  rcases hj with hLower | hUpper
  · exact topTruncationRaw_isZero_X_of_isZero (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK j
      (hSupport j (Or.inl hLower))
  · by_cases hTop : j = b
    · subst j
      exact topTruncationRaw_isZero_X_upper (b := b) (a := a) (hSupport := hSupport) F
        hKernelClosure K hK
    · exact topTruncationRaw_isZero_X_of_isZero (b := b) (a := a) (hSupport := hSupport) F
        hKernelClosure K hK j
        (hSupport j (Or.inr (by omega)))

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw kernel truncation T is bounded with the inherited lower bound and upper bound t−1. -/
theorem bounded_topTruncationRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CochainComplex.bounded E (topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK) :=
  ⟨a, b - 1, topTruncationRaw_support (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK⟩

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw cochain kernel T, with its proved finite support, is an object of Bounded(E). -/
def topTruncation (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : Bounded E :=
  ⟨topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK,
    bounded_topTruncationRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK⟩

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The kernel inclusion i:T → K is the corresponding bounded cochain morphism. -/
def topTruncationι (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncation (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ⟶ K :=
  ObjectProperty.homMk (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F
    hKernelClosure K hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The underlying map of the bounded truncation inclusion is the raw cochain kernel inclusion i. -/
theorem topTruncationι_hom (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).hom =
      topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK := rfl

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The bounded inclusion followed by the bounded disk projection is zero. -/
theorem topTruncationι_projection (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ≫
      topDiskProjectionBounded (b := b) K = 0 := by
  apply (fullyFaithfulι E).map_injective
  exact topTruncationRawι_projection (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw truncation short complex is T —i→ K —π→ D_t. -/
abbrev topTruncationRawShortComplex (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ShortComplex (CochainComplex E ℤ) :=
  ShortComplex.mk (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK) (topDiskProjection (b := b) K)
    (topTruncationRawι_projection (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Every term row T^j → K^j → D_t^j is admissible exact in E. -/
theorem topTruncationRawShortComplex_term_isAdmissibleExact (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleExact ((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK).map
      (HomologicalComplex.eval E (.up ℤ) j)) := by
  obtain ⟨Z, i, w, hS⟩ := topDiskProjection_isAdmissibleEpi (b := b) (a := a) (hSupport :=
    hSupport) F hKernelClosure K hK j
  let hKernel := isLimit_kernelFork_of_isAdmissibleExact hS
  let hActual := topTruncationTermIsLimit (b := b) (a := a) (hSupport := hSupport) F
    hKernelClosure K hK j
  let e := hKernel.conePointUniqueUpToIso hActual
  have he := IsLimit.conePointUniqueUpToIso_hom_comp hKernel hActual WalkingParallelPair.zero
  have he' : e.hom ≫ (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK).f j = i := he
  let eS : ShortComplex.mk i ((topDiskProjection (b := b) K).f j) w ≅
      (topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK).map
        (HomologicalComplex.eval E (.up ℤ) j) :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by
      change e.hom ≫ (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
        K hK).f j = i ≫ 𝟙 _
      rw [Category.comp_id]
      exact he') (by
      change 𝟙 _ ≫ (topDiskProjection (b := b) K).f j = (topDiskProjection (b := b) K).f j ≫ 𝟙 _
      simp)
  exact isAdmissibleExact_of_iso eS hS

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Every component of the bounded inclusion i:T → K is an admissible monomorphism. -/
theorem topTruncationι_isAdmissibleMono_f (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleMono ((topTruncationι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
      hK).hom.f j) :=
  isAdmissibleMono_f
    (topTruncationRawShortComplex_term_isAdmissibleExact (b := b) (a := a) (hSupport := hSupport)
      F hKernelClosure K hK j)

variable [F.IsExact]

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K. Assume also F is exact.

The mapped raw row 0 → F(T) → F(K) → F(D_t) → 0 is short exact in ambient cochain complexes. -/
theorem topTruncationRawShortComplex_map_shortExact (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
      hK).map
      (F.mapHomologicalComplex (.up ℤ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  change (((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK).map
    (HomologicalComplex.eval E (.up ℤ) j)).map F).ShortExact
  exact F.map_admissibleExact _
    (topTruncationRawShortComplex_term_isAdmissibleExact (b := b) (a := a) (hSupport := hSupport)
      F hKernelClosure K hK j)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K. Assume also F is exact.

The truncated complex F(T) is acyclic in the ambient category. -/
theorem topTruncation_map_acyclic (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
      (topTruncation (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).obj).Acyclic
        := by
  let S := (topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK).map
    (F.mapHomologicalComplex (.up ℤ))
  have hS : S.ShortExact := topTruncationRawShortComplex_map_shortExact (b := b) (a := a)
    (hSupport := hSupport) F hKernelClosure K hK
  intro j
  have hExact := hS.homology_exact₁ (j - 1) j (ComplexShape.up_mk _ _ (by omega))
  have hPrev : IsZero (S.X₃.homology (j - 1)) :=
    (topDisk_map_acyclic (b := b) F K (j - 1)).isZero_homology
  have hNext : IsZero (S.X₂.homology j) := (hK j).isZero_homology
  have hZero := hExact.isZero_X₂ (hPrev.eq_of_src _ _) (hNext.eq_of_tgt _ _)
  exact (S.X₁.exactAt_iff_isZero_homology j).mpr hZero

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw truncation cofiber is the homotopy cofiber Cofib(i) of the raw inclusion. -/
abbrev topTruncationCofiberRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : CochainComplex E ℤ :=
  HomologicalComplex.homotopyCofiber (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F
    hKernelClosure K hK)

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw cofiber Cofib(i) is bounded, using the finite support of T and K with the source shift by
one. -/
theorem bounded_topTruncationCofiberRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CochainComplex.bounded E (topTruncationCofiberRaw (b := b) (a := a) (hSupport := hSupport) F
      hKernelClosure K hK) := by
  refine ⟨a - 1, b, ?_⟩
  intro j hj
  apply HomologicalComplex.homotopyCofiber.isZero_X (topTruncationRawι (b := b) (a := a) (hSupport
    := hSupport) F hKernelClosure K hK) j
  · have hBound := hSupport j
    change (j < a ∨ b < j) → IsZero (K.obj.X j) at hBound
    exact hBound (by omega)
  · intro n hn
    change j + 1 = n at hn
    exact topTruncationRaw_support (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK
      n (by omega)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The homotopy cofiber Cofib(i), with its proved support, is the bounded truncation-cofiber object. -/
def topTruncationCofiber (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : Bounded E :=
  ⟨topTruncationCofiberRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK,
    bounded_topTruncationCofiberRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK⟩

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The descendant r:Cofib(i) → D_t is induced by π and the zero composite π∘i. -/
abbrev topTruncationCofiberDescRaw (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationCofiberRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ⟶
      topDiskRaw (b := b) K :=
  HomologicalComplex.homotopyCofiber.descShortComplex
    (topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK)

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The target inclusion K → Cofib(i) followed by r equals π. -/
theorem topTruncationCofiber_inr_desc (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    HomologicalComplex.homotopyCofiber.inr (topTruncationRawι (b := b) (a := a) (hSupport :=
      hSupport) F hKernelClosure K hK) ≫
      topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK =
        topDiskProjection (b := b) K := by
  exact HomologicalComplex.homotopyCofiber.inr_descShortComplex
    (topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK)

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Each shifted-source component of r:Cofib(i) → D_t is zero, from its defining zero homotopy. -/
theorem topTruncationCofiber_inlX_desc_f (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    HomologicalComplex.homotopyCofiber.inlX (topTruncationRawι (b := b) (a := a) (hSupport :=
      hSupport) F hKernelClosure K hK) j i hij ≫
      (topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK).f i = 0 := by
  let S := topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK
  change HomologicalComplex.homotopyCofiber.inlX S.f j i hij ≫
    (HomologicalComplex.homotopyCofiber.descShortComplex S).f i = 0
  rw [HomologicalComplex.homotopyCofiber.descShortComplex_f,
    HomologicalComplex.homotopyCofiber.inlX_sndX_assoc, zero_comp]

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw descendant r is the corresponding bounded morphism Cofib(i) → D_t. -/
def topTruncationCofiberDesc (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationCofiber (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK ⟶ topDisk
      (b := b) K :=
  ObjectProperty.homMk (topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F
    hKernelClosure K hK)

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Forgetting boundedness from the descendant returns the raw map r. -/
theorem topTruncationCofiberDesc_hom (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationCofiberDesc (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).hom =
      topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK
        := rfl

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The additive-functor comparison F(Cofib(i)) ≅ Cofib(F(i)) identifies the two cofiber constructions.
-/
abbrev topTruncationCofiberMapIso (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (F.mapHomologicalComplex (.up ℤ)).obj (topTruncationCofiberRaw (b := b) (a := a) (hSupport :=
      hSupport) F hKernelClosure K hK) ≅
      HomologicalComplex.homotopyCofiber
        ((F.mapHomologicalComplex (.up ℤ)).map (topTruncationRawι (b := b) (a := a) (hSupport :=
          hSupport) F hKernelClosure K hK)) :=
  HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso
    (topTruncationRawι (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK) F

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Under F(Cofib(i)) ≅ Cofib(F(i)), the mapped descendant F(r) equals the canonical descendant of the
mapped row F(T) → F(K) → F(D_t). -/
theorem topTruncationCofiberDesc_map (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationCofiberMapIso (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
      hK).hom ≫
      HomologicalComplex.homotopyCofiber.descShortComplex
        ((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
          hK).map
          (F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map (topTruncationCofiberDescRaw (b := b) (a := a)
        (hSupport := hSupport) F hKernelClosure K hK) := by
  let S := topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure
    K hK
  let J := F.mapHomologicalComplex (.up ℤ)
  let e : J.obj (HomologicalComplex.homotopyCofiber S.f) ≅
      HomologicalComplex.homotopyCofiber (S.map J).f :=
    HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso S.f F
  have he (j : ℤ) : e.inv.f j =
      (HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjXIso S.f F j).inv := rfl
  have hInv : e.inv ≫ J.map (HomologicalComplex.homotopyCofiber.descShortComplex S) =
      HomologicalComplex.homotopyCofiber.descShortComplex (S.map J) := by
    ext j
    change e.inv.f j ≫ F.map ((HomologicalComplex.homotopyCofiber.descShortComplex S).f j) =
      (HomologicalComplex.homotopyCofiber.descShortComplex (S.map J)).f j
    rw [he]
    apply HomologicalComplex.homotopyCofiber.ext_from_X (J.map S.f) (j + 1) j
      (ComplexShape.up_mk _ _ rfl)
    · rw [HomologicalComplex.homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv_assoc,
        ← F.map_comp, HomologicalComplex.homotopyCofiber.descShortComplex_f,
        HomologicalComplex.homotopyCofiber.inlX_sndX_assoc, zero_comp, F.map_zero]
      change 0 = HomologicalComplex.homotopyCofiber.inlX (S.map J).f (j + 1) j
        (ComplexShape.up_mk _ _ rfl) ≫
        (HomologicalComplex.homotopyCofiber.descShortComplex (S.map J)).f j
      rw [HomologicalComplex.homotopyCofiber.descShortComplex_f,
        HomologicalComplex.homotopyCofiber.inlX_sndX_assoc, zero_comp]
    · rw [HomologicalComplex.homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv_assoc,
        ← F.map_comp, HomologicalComplex.homotopyCofiber.descShortComplex_f,
        HomologicalComplex.homotopyCofiber.inrX_sndX_assoc]
      change (S.map J).g.f j = HomologicalComplex.homotopyCofiber.inrX (S.map J).f j ≫
        (HomologicalComplex.homotopyCofiber.descShortComplex (S.map J)).f j
      rw [HomologicalComplex.homotopyCofiber.descShortComplex_f,
        HomologicalComplex.homotopyCofiber.inrX_sndX_assoc]
  change e.hom ≫ HomologicalComplex.homotopyCofiber.descShortComplex (S.map J) =
    J.map (HomologicalComplex.homotopyCofiber.descShortComplex S)
  apply (cancel_epi e.inv).mp
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact hInv.symm

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K. Assume also F is exact.

The image under F of the bounded descendant r:Cofib(i) → D_t is a quasi-isomorphism. -/
theorem topTruncationCofiberDesc_map_quasiIso (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (topTruncationCofiberDesc (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK).hom) := by
  change QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
    (topTruncationCofiberDescRaw (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK))
  rw [← topTruncationCofiberDesc_map (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK]
  exact quasiIso_comp
    (hφ := (inferInstance : QuasiIso (topTruncationCofiberMapIso (b := b) (a := a) (hSupport :=
      hSupport) F hKernelClosure K hK).hom))
    (hφ' := HomologicalComplex.homotopyCofiber.quasiIso_descShortComplex_up _
      (topTruncationRawShortComplex_map_shortExact (b := b) (a := a) (hSupport := hSupport) F
        hKernelClosure K hK))
    (topTruncationCofiberMapIso (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).hom
    (HomologicalComplex.homotopyCofiber.descShortComplex
      ((topTruncationRawShortComplex (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
        hK).map
        (F.mapHomologicalComplex (.up ℤ))))

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t=b is a supplied integer.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E →
A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the supplied support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The kernel retains the lower bound a and has the strictly smaller upper bound b−1<b: its terms are
zero outside [a,b−1]. -/
theorem topTruncation_strict_support (K : Bounded E)
    (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    b - 1 < b ∧ ∀ j : ℤ, j < a ∨ b - 1 < j →
      IsZero ((topTruncation (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K hK).obj.X
        j) :=
  ⟨by omega, topTruncationRaw_support (b := b) (a := a) (hSupport := hSupport) F hKernelClosure K
    hK⟩

end CochainComplex.Bounded.TruncationAt

end
