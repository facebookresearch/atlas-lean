/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveImages
public import MathlibExt.Algebra.Homology.ChainGradedPairingStrictPositive
public import MathlibExt.Algebra.Homology.TensorUnitor
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Positive image quotients and truncation comparisons

Let R be a ring, equip ModuleCat R with an additive monoidal structure, and let
P : K₁ ⊗ K₂ → K₃ be a pairing of nonnegative chain complexes. In degree n, the relation
submodule is the sum of the images of P_{p,q} for p,q>0 and p+q=n. If d_K₁,1,0 and
d_K₂,1,0 vanish, these submodules form a subcomplex and their quotients inherit the
differential of K₃. The degree-zero objects of the three complexes are unrestricted.

The projection onto this image quotient is a cokernel of the strict-positive pairing.
It therefore identifies the image quotient with the strict-positive cokernel and,
through the smart-to-stupid truncation comparison, with the smart-positive truncation
quotient. The comparisons preserve the projection from K₃ and are natural under maps
of compatible pairings.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [CategoryTheory.MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- The original differential restricted to the actual positive image family. -/
def positiveImageDifferential (n : ℕ) :
    ModuleCat.of R (positiveImages P (n + 1)) ⟶ ModuleCat.of R (positiveImages P n) :=
  ModuleCat.ofHom
    (((K₃.d (n + 1) n).hom.comp (positiveImages P (n + 1)).subtype).codRestrict
      (positiveImages P n) (fun x => positiveImages_d P h₁ h₂ n x.property))

/-- The restricted maps square to zero because the original differential does. -/
theorem positiveImageDifferential_comp (n : ℕ) :
    positiveImageDifferential P h₁ h₂ (n + 1) ≫
      positiveImageDifferential P h₁ h₂ n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (K₃.d (n + 1) n).hom ((K₃.d (n + 2) (n + 1)).hom x.val) = 0
  have hd : (K₃.d (n + 1) n).hom.comp (K₃.d (n + 2) (n + 1)).hom = 0 :=
    congrArg ModuleCat.Hom.hom (K₃.d_comp_d (n + 2) (n + 1) n)
  exact congrArg (fun f : K₃.X (n + 2) →ₗ[R] K₃.X n => f x.val) hd

/-- The subcomplex on D_n = sum of positive component images. -/
def positiveImageSubcomplex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (positiveImages P n))
    (positiveImageDifferential P h₁ h₂) (positiveImageDifferential_comp P h₁ h₂)

/-- The subcomplex inclusion is the native subtype map in every degree. -/
def positiveImageInclusion : positiveImageSubcomplex P h₁ h₂ ⟶ K₃ :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (positiveImages P n).subtype) (by
    intro n
    apply ModuleCat.hom_ext
    ext x
    simp only [positiveImageSubcomplex, ChainComplex.of_d]
    rfl)

/-- The quotient boundary is the native induced map of the original differential. -/
def positiveQuotientDifferential (n : ℕ) :
    ModuleCat.of R ((K₃.X (n + 1)) ⧸ positiveImages P (n + 1)) ⟶
      ModuleCat.of R ((K₃.X n) ⧸ positiveImages P n) :=
  ModuleCat.ofHom ((positiveImages P (n + 1)).mapQ (positiveImages P n)
    (K₃.d (n + 1) n).hom (positiveImages_d P h₁ h₂ n))

/-- The quotient maps inherit d squared equals zero from the original complex. -/
theorem positiveQuotientDifferential_comp (n : ℕ) :
    positiveQuotientDifferential P h₁ h₂ (n + 1) ≫
      positiveQuotientDifferential P h₁ h₂ n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  change (positiveImages P n).mkQ
    ((K₃.d (n + 1) n).hom ((K₃.d (n + 2) (n + 1)).hom x)) = 0
  have hd : (K₃.d (n + 1) n).hom.comp (K₃.d (n + 2) (n + 1)).hom = 0 :=
    congrArg ModuleCat.Hom.hom (K₃.d_comp_d (n + 2) (n + 1) n)
  have hx : (K₃.d (n + 1) n).hom ((K₃.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun f : K₃.X (n + 2) →ₗ[R] K₃.X n => f x) hd
  rw [hx, map_zero]

/-- The actual pointwise quotient K_3,n / D_n, retaining the full original target complex. -/
def positiveImageQuotient : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R ((K₃.X n) ⧸ positiveImages P n))
    (positiveQuotientDifferential P h₁ h₂) (positiveQuotientDifferential_comp P h₁ h₂)

/-- The original target maps to its quotient through its actual quotient maps. -/
def positiveImageProjection : K₃ ⟶ positiveImageQuotient P h₁ h₂ :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (positiveImages P n).mkQ) (by
    intro n
    apply ModuleCat.hom_ext
    simp only [positiveImageQuotient, ChainComplex.of_d]
    exact Submodule.mapQ_mkQ (positiveImages P (n + 1)) (positiveImages P n)
      (K₃.d (n + 1) n).hom (h := positiveImages_d P h₁ h₂ n))

/-- Its actual component kernel is exactly the stated positive relation family. -/
theorem ker_positiveImageProjection (n : ℕ) :
    LinearMap.ker ((positiveImageProjection P h₁ h₂).f n).hom = positiveImages P n :=
  Submodule.ker_mkQ _

/-- Every original positive pairing component is killed by the actual quotient projection. -/
theorem pairAt_comp_positiveImageProjection (p q n : ℕ) (h : p + q = n)
    (hp : 0 < p) (hq : 0 < q) :
    pairAt P p q n h ≫ (positiveImageProjection P h₁ h₂).f n = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change (positiveImages P n).mkQ ((pairAt P p q n h).hom x) = 0
  have hm := pairAt_mem_positiveImages P p q n h hp hq x
  have hk : (pairAt P p q n h).hom x ∈ LinearMap.ker (positiveImages P n).mkQ := by
    simpa only [Submodule.ker_mkQ] using hm
  exact hk

/-- D_0 is zero, so the quotient never destroys the original degree-zero object. -/
theorem positiveImageProjection_injective_zero :
    Function.Injective ((positiveImageProjection P h₁ h₂).f 0).hom := by
  apply LinearMap.ker_eq_bot.mp
  rw [ker_positiveImageProjection, positiveImages_zero]

/-- D_1 is also zero; the original degree-one coordinate is retained. -/
theorem positiveImageProjection_injective_one :
    Function.Injective ((positiveImageProjection P h₁ h₂).f 1).hom := by
  apply LinearMap.ker_eq_bot.mp
  rw [ker_positiveImageProjection, positiveImages_one]

section Naturality

variable {L₁ L₂ L₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (Q : ChainGradedPairing L₁ L₂ L₃)
  (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
  (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)

/-- A morphism of pairings induces the native quotient map componentwise. -/
def positiveImageQuotientMap :
    positiveImageQuotient P h₁ h₂ ⟶ positiveImageQuotient Q g₁ g₂ :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((positiveImages P n).mapQ (positiveImages Q n) (f₃.f n).hom
      (positiveImages_naturality P Q f₁ f₂ f₃ hf n))) (by
    intro n
    apply ModuleCat.hom_ext
    ext z
    refine Quotient.inductionOn' z ?_
    intro x
    simp only [positiveImageQuotient, ChainComplex.of_d]
    change (positiveImages Q n).mkQ
      ((L₃.d (n + 1) n).hom ((f₃.f (n + 1)).hom x)) =
        (positiveImages Q n).mkQ ((f₃.f n).hom ((K₃.d (n + 1) n).hom x))
    exact congrArg (positiveImages Q n).mkQ
      (ConcreteCategory.congr_hom (f₃.comm (n + 1) n) x))

/-- The actual induced map commutes with the original target maps and projections. -/
@[reassoc]
theorem positiveImageProjection_map :
    positiveImageProjection P h₁ h₂ ≫
        positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf =
      f₃ ≫ positiveImageProjection Q g₁ g₂ := by
  ext n x
  rfl

end Naturality

/-- The identity morphism of a pairing induces the identity on the actual quotient. -/
@[simp]
theorem positiveImageQuotientMap_id :
    positiveImageQuotientMap P h₁ h₂ P h₁ h₂ (𝟙 K₁) (𝟙 K₂) (𝟙 K₃)
      (by simp only [tensorHom_id_id, Category.id_comp, Category.comp_id]) =
        𝟙 (positiveImageQuotient P h₁ h₂) := by
  ext n z
  refine Quotient.inductionOn' z ?_
  intro x
  rfl

/-- Actual compatible composition of pairings gives composition of the native quotient maps. -/
@[reassoc]
theorem positiveImageQuotientMap_comp
    {L₁ L₂ L₃ M₁ M₂ M₃ : ChainComplex (ModuleCat.{v} R) ℕ}
    (Q : ChainGradedPairing L₁ L₂ L₃) (S : ChainGradedPairing M₁ M₂ M₃)
    (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
    (s₁ : M₁.d 1 0 = 0) (s₂ : M₂.d 1 0 = 0)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (k₁ : L₁ ⟶ M₁) (k₂ : L₂ ⟶ M₂) (k₃ : L₃ ⟶ M₃)
    (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃)
    (hk : tensorHom k₁ k₂ ≫ S = Q ≫ k₃) :
    positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf ≫
        positiveImageQuotientMap Q g₁ g₂ S s₁ s₂ k₁ k₂ k₃ hk =
      positiveImageQuotientMap P h₁ h₂ S s₁ s₂ (f₁ ≫ k₁) (f₂ ≫ k₂) (f₃ ≫ k₃)
        (by rw [← tensorHom_comp_tensorHom, Category.assoc, hk,
          ← Category.assoc, hf, Category.assoc]) := by
  ext n z
  refine Quotient.inductionOn' z ?_
  intro x
  rfl

/-- Let R be a ring and give ModuleCat R an additive monoidal structure. For a pairing
P of nonnegative chain complexes with both degree-one boundaries zero, its strict-positive
component in bidegree (p,q), total degree n=p+q, is the original component preceded by
the two positive-truncation inclusions. -/
theorem pairAt_strictPositivePairing (p q n : ℕ) (h : p + q = n) :
    pairAt (strictPositivePairing P h₁ h₂) p q n h =
      ((K₁.positiveStupidTruncInclusion h₁).f p ⊗ₘ
        (K₂.positiveStupidTruncInclusion h₂).f q) ≫ pairAt P p q n h := by
  simp only [pairAt, strictPositivePairing, HomologicalComplex.comp_f]
  rw [← Category.assoc, ιTensorObj_tensorHom, Category.assoc]

/-- Over a ring R, for an additive monoidal structure on ModuleCat R and a nonnegative
chain pairing with both degree-one boundaries zero, the strict-positive pairing is
annihilated by the projection to the quotient by all both-positive component images. -/
@[reassoc]
theorem strictPositivePairing_comp_positiveImageProjection :
    strictPositivePairing P h₁ h₂ ≫ positiveImageProjection P h₁ h₂ = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change (strictPositivePairing P h₁ h₂).f n ≫
    (positiveImageProjection P h₁ h₂).f n = 0
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := K₁.stupidTrunc ComplexShape.positiveNatEmbedding)
    (K₂ := K₂.stupidTrunc ComplexShape.positiveNatEmbedding)
    (F := curriedTensor (ModuleCat.{v} R)) (c := ComplexShape.down ℕ)
  intro p q h
  simp only [comp_zero]
  rw [← Category.assoc]
  change pairAt (strictPositivePairing P h₁ h₂) p q n h ≫
    (positiveImageProjection P h₁ h₂).f n = 0
  rw [pairAt_strictPositivePairing, Category.assoc]
  cases p with
  | zero => simp [positiveStupidTruncInclusion_f_zero]
  | succ p =>
    cases q with
    | zero => simp [positiveStupidTruncInclusion_f_zero]
    | succ q =>
      rw [pairAt_comp_positiveImageProjection P h₁ h₂ (p + 1) (q + 1) n h
        (Nat.succ_pos p) (Nat.succ_pos q), comp_zero]

/-- Let R be a ring and give ModuleCat R an additive monoidal structure. For a nonnegative
chain pairing P whose two degree-one boundaries vanish, the image of its strict-positive
map in degree n is exactly the sum of the images of P_{p,q} over p,q>0 and p+q=n. -/
theorem range_strictPositivePairing (n : ℕ) :
    LinearMap.range ((strictPositivePairing P h₁ h₂).f n).hom = positiveImages P n := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    rw [← ker_positiveImageProjection P h₁ h₂ n]
    change ((positiveImageProjection P h₁ h₂).f n).hom
      (((strictPositivePairing P h₁ h₂).f n).hom x) = 0
    have h := congrArg
      (fun f : tensorObj (K₁.stupidTrunc ComplexShape.positiveNatEmbedding)
          (K₂.stupidTrunc ComplexShape.positiveNatEmbedding) ⟶
          positiveImageQuotient P h₁ h₂ => f.f n)
      (strictPositivePairing_comp_positiveImageProjection P h₁ h₂)
    change (strictPositivePairing P h₁ h₂).f n ≫
      (positiveImageProjection P h₁ h₂).f n = 0 at h
    exact ConcreteCategory.congr_hom h x
  · rw [positiveImages]
    apply iSup_le
    rintro ⟨⟨p, q⟩, hp, hq, hn⟩
    cases p with
    | zero => omega
    | succ p =>
      cases q with
      | zero => omega
      | succ q =>
        rintro z ⟨x, rfl⟩
        let e₁ := K₁.stupidTruncXIso ComplexShape.positiveNatEmbedding
          (i := p) (i' := p + 1) rfl
        let e₂ := K₂.stupidTruncXIso ComplexShape.positiveNatEmbedding
          (i := q) (i' := q + 1) rfl
        let eT :
            (K₁.stupidTrunc ComplexShape.positiveNatEmbedding).X (p + 1) ⊗
              (K₂.stupidTrunc ComplexShape.positiveNatEmbedding).X (q + 1) ≅
            K₁.X (p + 1) ⊗ K₂.X (q + 1) :=
          MonoidalCategory.tensorIso e₁ e₂
        let y := eT.inv.hom x
        refine ⟨(ιTensorObj (K₁.stupidTrunc ComplexShape.positiveNatEmbedding)
          (K₂.stupidTrunc ComplexShape.positiveNatEmbedding) (p + 1) (q + 1) n hn).hom y, ?_⟩
        have h := pairAt_strictPositivePairing P h₁ h₂ (p + 1) (q + 1) n hn
        rw [K₁.positiveStupidTruncInclusion_f h₁ (i := p) rfl,
          K₂.positiveStupidTruncInclusion_f h₂ (i := q) rfl] at h
        change pairAt (strictPositivePairing P h₁ h₂) (p + 1) (q + 1) n hn =
          eT.hom ≫ pairAt P (p + 1) (q + 1) n hn at h
        have hy : eT.hom.hom y = x := ConcreteCategory.congr_hom eT.inv_hom_id x
        exact (ConcreteCategory.congr_hom h y).trans
          (congrArg (pairAt P (p + 1) (q + 1) n hn).hom hy)

/-- Let R be a ring and equip ModuleCat R with an additive monoidal structure. For a pairing
P of nonnegative chain complexes with both degree-one boundaries zero, the projection
K₃ → positiveImageQuotient P is a cokernel of the strict-positive pairing. -/
def positiveImageProjectionIsCokernel :
    IsColimit (CokernelCofork.ofπ (positiveImageProjection P h₁ h₂)
      (strictPositivePairing_comp_positiveImageProjection P h₁ h₂)) := by
  refine HomologicalComplex.isColimitOfEval _ _ (fun n => ?_)
  have hExact : Function.Exact ((strictPositivePairing P h₁ h₂).f n).hom
      ((positiveImageProjection P h₁ h₂).f n).hom :=
    LinearMap.exact_iff.mpr
      ((ker_positiveImageProjection P h₁ h₂ n).trans
        (range_strictPositivePairing P h₁ h₂ n).symm)
  have hSurjective : Function.Surjective ((positiveImageProjection P h₁ h₂).f n).hom := by
    change Function.Surjective (positiveImages P n).mkQ
    exact (positiveImages P n).mkQ_surjective
  change IsColimit (CokernelCofork.ofπ (f := (strictPositivePairing P h₁ h₂).f n)
    ((positiveImageProjection P h₁ h₂).f n) _)
  exact ModuleCat.isColimitCokernelCofork
    ((strictPositivePairing P h₁ h₂).f n) ((positiveImageProjection P h₁ h₂).f n)
    hExact hSurjective

/-- For an additive monoidal structure on ModuleCat R, a nonnegative chain pairing P with
vanishing degree-one boundaries in both inputs has a canonical isomorphism from its
strict-positive cokernel to the quotient by the sum of both-positive component images.
The isomorphism induces the identity on the target complex K₃. -/
def strictPositiveCokernelIsoPositiveImageQuotient :
    strictPositiveCokernel P h₁ h₂ ≅ positiveImageQuotient P h₁ h₂ :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (strictPositivePairing P h₁ h₂))
    (positiveImageProjectionIsCokernel P h₁ h₂)

/-- For a nonnegative chain pairing in an additive monoidal category of R-modules with
both degree-one boundaries zero, the strict-positive projection followed by its
image-quotient comparison is the projection from K₃ to the positive image quotient. -/
@[reassoc]
theorem strictPositiveProjection_isoPositiveImage_hom :
    strictPositiveProjection P h₁ h₂ ≫
        (strictPositiveCokernelIsoPositiveImageQuotient P h₁ h₂).hom =
      positiveImageProjection P h₁ h₂ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (strictPositivePairing P h₁ h₂))
    (positiveImageProjectionIsCokernel P h₁ h₂) WalkingParallelPair.one

/-- For a nonnegative chain pairing over R with an additive monoidal module structure and
zero degree-one boundaries in both inputs, the positive image projection followed by
the inverse comparison equals the strict-positive projection from K₃. -/
@[reassoc]
theorem positiveImageProjection_isoStrictPositive_inv :
    positiveImageProjection P h₁ h₂ ≫
        (strictPositiveCokernelIsoPositiveImageQuotient P h₁ h₂).inv =
      strictPositiveProjection P h₁ h₂ := by
  apply (cancel_mono (strictPositiveCokernelIsoPositiveImageQuotient P h₁ h₂).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (strictPositiveProjection_isoPositiveImage_hom P h₁ h₂).symm

/-- Let R be a ring with an additive monoidal structure on ModuleCat R. For a nonnegative
chain pairing P with both degree-one boundaries zero, the smart-positive truncation
quotient is canonically isomorphic to the quotient by all component images in bidegrees
p,q>0. This is the composite of the smart/strict and strict/image comparisons. -/
def truncationQuotientIsoPositiveImageQuotient :
    truncationQuotient ComplexShape.positiveNatEmbedding P ≅ positiveImageQuotient P h₁ h₂ :=
  truncationQuotientIsoStrictPositiveCokernel P h₁ h₂ ≪≫
    strictPositiveCokernelIsoPositiveImageQuotient P h₁ h₂

/-- For a pairing of nonnegative R-module complexes with additive tensor structure and
zero degree-one boundaries in both inputs, the smart-positive projection followed by
its comparison with the positive image quotient equals the positive image projection. -/
@[reassoc]
theorem truncationProjection_isoPositiveImage_hom :
    truncationProjection ComplexShape.positiveNatEmbedding P ≫
        (truncationQuotientIsoPositiveImageQuotient P h₁ h₂).hom =
      positiveImageProjection P h₁ h₂ := by
  rw [truncationQuotientIsoPositiveImageQuotient, Iso.trans_hom, ← Category.assoc,
    truncationProjection_isoStrictPositive_hom, strictPositiveProjection_isoPositiveImage_hom]

/-- Let P and Q pair nonnegative chain complexes of R-modules with an additive monoidal
structure, and assume the two input degree-one boundaries vanish for each pairing.
If f₁,f₂,f₃ are chain maps satisfying tensorHom(f₁,f₂) ≫ Q = P ≫ f₃, then the smart/image
comparison commutes with the induced smart-truncation quotient map and the induced
positive-image quotient map. -/
@[reassoc]
theorem truncationQuotientIsoPositiveImageQuotient_naturality
    {L₁ L₂ L₃ : ChainComplex (ModuleCat.{v} R) ℕ}
    (Q : ChainGradedPairing L₁ L₂ L₃)
    (g₁ : L₁.d 1 0 = 0) (g₂ : L₂.d 1 0 = 0)
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (hf : tensorHom f₁ f₂ ≫ Q = P ≫ f₃) :
    truncationQuotientMap ComplexShape.positiveNatEmbedding P Q f₁ f₂ f₃ hf ≫
        (truncationQuotientIsoPositiveImageQuotient Q g₁ g₂).hom =
      (truncationQuotientIsoPositiveImageQuotient P h₁ h₂).hom ≫
        positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf := by
  let _ : Epi (truncationProjection ComplexShape.positiveNatEmbedding P) := by
    change Epi (cokernel.π (truncationPairing ComplexShape.positiveNatEmbedding P))
    infer_instance
  apply (cancel_epi (truncationProjection ComplexShape.positiveNatEmbedding P)).1
  calc
    truncationProjection ComplexShape.positiveNatEmbedding P ≫
        (truncationQuotientMap ComplexShape.positiveNatEmbedding P Q f₁ f₂ f₃ hf ≫
          (truncationQuotientIsoPositiveImageQuotient Q g₁ g₂).hom) =
        (truncationProjection ComplexShape.positiveNatEmbedding P ≫
          truncationQuotientMap ComplexShape.positiveNatEmbedding P Q f₁ f₂ f₃ hf) ≫
            (truncationQuotientIsoPositiveImageQuotient Q g₁ g₂).hom := (Category.assoc _ _ _).symm
    _ = (f₃ ≫ truncationProjection ComplexShape.positiveNatEmbedding Q) ≫
        (truncationQuotientIsoPositiveImageQuotient Q g₁ g₂).hom := by
          rw [truncationProjection_map]
    _ = f₃ ≫ positiveImageProjection Q g₁ g₂ := by
      rw [Category.assoc, truncationProjection_isoPositiveImage_hom]
    _ = positiveImageProjection P h₁ h₂ ≫
        positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf :=
      (positiveImageProjection_map P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf).symm
    _ = truncationProjection ComplexShape.positiveNatEmbedding P ≫
        ((truncationQuotientIsoPositiveImageQuotient P h₁ h₂).hom ≫
          positiveImageQuotientMap P h₁ h₂ Q g₁ g₂ f₁ f₂ f₃ hf) := by
            rw [← Category.assoc, truncationProjection_isoPositiveImage_hom]

end HomologicalComplex.ChainGradedPairing
