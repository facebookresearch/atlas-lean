/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicTruncationAt

/-!
# Top disk and kernel truncation at a selected cutoff

Let E be preadditive with a zero object and binary biproducts.
For a bounded complex K with selected support endpoint t, let S_t be
the single complex on K^t and D_t=Cofib(1_{S_t}).
The top-term degree-zero cochain f₀ and its negative boundary h=−∂f₀
give the chain projection π:K → D_t. Its upper component is the
upper identity chart and its lower component is the original incoming
differential with positive sign.

For a Quillen exact structure on E and a fully faithful additive embedding F
into an abelian category,
essential-image closure under kernels of epimorphisms and reflection
of admissible exactness make the projection degreewise admissible epic
when F(K) is acyclic. Its cochain kernel is bounded with upper support
endpoint t−1. If F is exact, this kernel remains ambient acyclic and
the cofiber descendant to D_t becomes a quasi-isomorphism under F.
All source and ambient category universes are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CochainComplex.HomComplex
open scoped ZeroObject

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E]

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The top single complex S_t has K^t in degree t and zero terms elsewhere. -/
abbrev topDiskSingle (K : Bounded E) : CochainComplex E ℤ :=
  TruncationAt.topDiskSingle (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The raw top disk is the homotopy cofiber D_t of the identity of S_t. -/
abbrev topDiskRaw (K : Bounded E) : CochainComplex E ℤ :=
  TruncationAt.topDiskRaw (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The disk term D_t^j is zero for j≠t−1 and j≠t. -/
theorem topDisk_isZero_X (K : Bounded E) (j : ℤ)
    (hLower : j ≠ topCutoff K - 1) (hUpper : j ≠ topCutoff K) :
    IsZero ((topDiskRaw K).X j) :=
  TruncationAt.topDisk_isZero_X (b := topCutoff K) (K := K) (j := j) (hLower := hLower) (hUpper :=
    hUpper)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The canonical lower chart ℓ identifies K^t with D_t^{t−1}. -/
abbrev topDiskLowerIso (K : Bounded E) :
    K.obj.X (topCutoff K) ≅ (topDiskRaw K).X (topCutoff K - 1) :=
  TruncationAt.topDiskLowerIso (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The canonical upper chart u identifies K^t with D_t^t. -/
abbrev topDiskUpperIso (K : Bounded E) :
    K.obj.X (topCutoff K) ≅ (topDiskRaw K).X (topCutoff K) :=
  TruncationAt.topDiskUpperIso (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The lower chart is the single-term identification followed by the shifted-source cofiber inclusion. -/
theorem topDiskLowerIso_hom (K : Bounded E) :
    (topDiskLowerIso K).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (topCutoff K)
        (K.obj.X (topCutoff K))).inv ≫
      HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle K))
        (topCutoff K) (topCutoff K - 1)
        (ComplexShape.up_mk _ _ (by omega)) :=
  TruncationAt.topDiskLowerIso_hom (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The upper chart is the single-term identification followed by the target cofiber inclusion. -/
theorem topDiskUpperIso_hom (K : Bounded E) :
    (topDiskUpperIso K).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (topCutoff K)
        (K.obj.X (topCutoff K))).inv ≫
      HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle K)) (topCutoff K) :=
  TruncationAt.topDiskUpperIso_hom (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The disk differential satisfies d_D^{t−1}∘ℓ=u, so it is positive identity in these two charts. -/
theorem topDiskLowerIso_hom_d (K : Bounded E) :
    (topDiskLowerIso K).hom ≫ (topDiskRaw K).d (topCutoff K - 1) (topCutoff K) =
      (topDiskUpperIso K).hom :=
  TruncationAt.topDiskLowerIso_hom_d (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The degree-zero cochain f₀:K → S_t is identity in the top term and zero in other degrees. -/
abbrev topDiskCochain (K : Bounded E) : Cochain K.obj (topDiskSingle K) 0 :=
  TruncationAt.topDiskCochain (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The degree-one cocycle h=−∂f₀, the negative Hom-complex boundary of the top-term cochain, supplies the shifted-source cone coordinate. -/
abbrev topDiskBoundary (K : Bounded E) : Cocycle K.obj (topDiskSingle K) 1 :=
  TruncationAt.topDiskBoundary (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The chain map π:K → D_t is the cone lift formed from f₀ and h=−∂f₀. -/
abbrev topDiskProjection (K : Bounded E) : K.obj ⟶ topDiskRaw K :=
  TruncationAt.topDiskProjection (b := topCutoff K) (K := K)

omit [HasBinaryBiproducts E] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The top component of f₀ is the inverse single-term identification K^t → S_t^t. -/
theorem topDiskCochain_self (K : Bounded E) :
    (topDiskCochain K).v (topCutoff K) (topCutoff K) (add_zero _) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (topCutoff K)
        (K.obj.X (topCutoff K))).inv :=
  TruncationAt.topDiskCochain_self (b := topCutoff K) (K := K)

omit [HasBinaryBiproducts E] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The component of f₀ is zero in every degree j≠t. -/
theorem topDiskCochain_ne (K : Bounded E) (j : ℤ) (hj : j ≠ topCutoff K) :
    (topDiskCochain K).v j j (add_zero _) = 0 :=
  TruncationAt.topDiskCochain_ne (b := topCutoff K) (K := K) (j := j) (hj := hj)

omit [HasBinaryBiproducts E] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

For p+1=q, the negative boundary has component h_{p,q}=f₀,q∘d_K(p,q), with positive differential sign. -/
theorem topDiskBoundary_v (K : Bounded E) (p q : ℤ) (hpq : p + 1 = q) :
    (topDiskBoundary K).1.v p q hpq =
      K.obj.d p q ≫ (topDiskCochain K).v q q (add_zero _) :=
  TruncationAt.topDiskBoundary_v (b := topCutoff K) (K := K) (p := p) (q := q) (hpq := hpq)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

In degree j the projection π_j is the sum of h_{j,j+1} followed by the shifted-source inclusion and f₀,j followed by the target inclusion. -/
theorem topDiskProjection_f (K : Bounded E) (j : ℤ) :
    (topDiskProjection K).f j =
      (topDiskBoundary K).1.v j (j + 1) rfl ≫
          HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle K)) (j + 1) j rfl +
        (topDiskCochain K).v j j (add_zero j) ≫
          HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle K)) j :=
  TruncationAt.topDiskProjection_f (b := topCutoff K) (K := K) (j := j)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

For p+1=q, the projection π_p equals the shifted-source inclusion composed with h_{p,q}, plus the target inclusion composed with f₀,p. -/
theorem topDiskProjection_f' (K : Bounded E) (p q : ℤ) (hpq : p + 1 = q) :
    (topDiskProjection K).f p =
      (topDiskBoundary K).1.v p q hpq ≫
          HomologicalComplex.homotopyCofiber.inlX (𝟙 (topDiskSingle K)) q p
            (ComplexShape.up_mk _ _ hpq) +
        (topDiskCochain K).v p p (add_zero p) ≫
          HomologicalComplex.homotopyCofiber.inrX (𝟙 (topDiskSingle K)) p :=
  TruncationAt.topDiskProjection_f' (b := topCutoff K) (K := K) (p := p) (q := q) (hpq := hpq)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The upper projection component π_t equals the upper chart u. -/
theorem topDiskProjection_f_upper (K : Bounded E) :
    (topDiskProjection K).f (topCutoff K) = (topDiskUpperIso K).hom :=
  TruncationAt.topDiskProjection_f_upper (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The lower component is π_{t−1}=ℓ∘d_K^{t−1}, with positive sign. -/
theorem topDiskProjection_f_lower (K : Bounded E) :
    (topDiskProjection K).f (topCutoff K - 1) =
      K.obj.d (topCutoff K - 1) (topCutoff K) ≫ (topDiskLowerIso K).hom :=
  TruncationAt.topDiskProjection_f_lower (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The upper projection component π_t is an isomorphism. -/
theorem topDiskProjection_isIso_upper (K : Bounded E) :
    IsIso ((topDiskProjection K).f (topCutoff K)) :=
  TruncationAt.topDiskProjection_isIso_upper (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The raw disk has finite support [t−1,t] and is bounded. -/
theorem bounded_topDiskRaw (K : Bounded E) : CochainComplex.bounded E (topDiskRaw K) :=
  TruncationAt.bounded_topDiskRaw (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The identity cofiber D_t, with its support [t−1,t], is an object of the bounded cochain category. -/
abbrev topDisk (K : Bounded E) : Bounded E :=
  TruncationAt.topDisk (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The projection π:K → D_t is the corresponding morphism of bounded complexes. -/
abbrev topDiskProjectionBounded (K : Bounded E) : K ⟶ topDisk K :=
  TruncationAt.topDiskProjectionBounded (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

Forgetting boundedness from the bounded projection gives the original chain map π:K → D_t. -/
theorem topDiskProjectionBounded_hom (K : Bounded E) :
    (topDiskProjectionBounded K).hom = topDiskProjection K :=
  TruncationAt.topDiskProjectionBounded_hom (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts.

The top disk admits the canonical homotopy from its identity to zero, as the cofiber of an identity map. -/
abbrev topDiskContraction (K : Bounded E) :
    _root_.Homotopy (𝟙 (topDiskRaw K)) 0 :=
  TruncationAt.topDiskContraction (b := topCutoff K) (K := K)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Let F:E → A be any additive functor with A abelian.

The ambient image F(D_t) is acyclic. -/
theorem topDisk_map_acyclic {A : Type uA} [Category.{vA} A] [Abelian A]
    (F : E ⥤ A) [F.Additive] (K : Bounded E) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (topDiskRaw K)).Acyclic :=
  TruncationAt.topDisk_map_acyclic (b := topCutoff K) (F := F) (K := K)

variable [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

include hKernelClosure

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Every component π_j is an admissible epimorphism in E. -/
theorem topDiskProjection_isAdmissibleEpi (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleEpi ((topDiskProjection K).f j) :=
  TruncationAt.topDiskProjection_isAdmissibleEpi (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

For every degree j, the kernel of the component π_j exists in E. -/
theorem topDiskProjection_hasKernel_f (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    HasKernel ((topDiskProjection K).f j) :=
  TruncationAt.topDiskProjection_hasKernel_f (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The kernel of π exists in the category of integer cochain complexes, computed from its component kernels. -/
theorem topDiskProjection_hasKernel (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    HasKernel (topDiskProjection K) :=
  TruncationAt.topDiskProjection_hasKernel (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw upper truncation is T=Ker(π), with its cochain differential induced from K. -/
abbrev topTruncationRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : CochainComplex E ℤ :=
  TruncationAt.topTruncationRaw (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure) (a
    := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw truncation inclusion is the cochain kernel map i:T → K. -/
abbrev topTruncationRawι (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationRaw F hKernelClosure K hK ⟶ K.obj :=
  TruncationAt.topTruncationRawι (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure) (a
    := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The projection kills the kernel inclusion: π∘i=0. -/
theorem topTruncationRawι_projection (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationRawι F hKernelClosure K hK ≫ topDiskProjection K = 0 :=
  TruncationAt.topTruncationRawι_projection (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The inclusion i:T → K is a kernel of π in the cochain category. -/
abbrev topTruncationKernelIsLimit (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsLimit (KernelFork.ofι (f := topDiskProjection K)
      (topTruncationRawι F hKernelClosure K hK)
      (topTruncationRawι_projection F hKernelClosure K hK)) :=
  TruncationAt.topTruncationKernelIsLimit (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

In every degree j, i_j:T^j → K^j is a kernel of π_j. -/
abbrev topTruncationTermIsLimit (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsLimit (KernelFork.ofι (f := (topDiskProjection K).f j)
      ((topTruncationRawι F hKernelClosure K hK).f j) (by
        exact congrArg (fun t => t.f j) (topTruncationRawι_projection F hKernelClosure K hK))) :=
  TruncationAt.topTruncationTermIsLimit (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

If K^j is zero, the kernel term T^j is zero. -/
theorem topTruncationRaw_isZero_X_of_isZero (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ)
    (hj : IsZero (K.obj.X j)) :
    IsZero ((topTruncationRaw F hKernelClosure K hK).X j) :=
  TruncationAt.topTruncationRaw_isZero_X_of_isZero (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j) (hj := hj)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The upper kernel term T^t is zero because π_t is invertible. -/
theorem topTruncationRaw_isZero_X_upper (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    IsZero ((topTruncationRaw F hKernelClosure K hK).X (topCutoff K)) :=
  TruncationAt.topTruncationRaw_isZero_X_upper (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The kernel truncation has support [a,t−1]. -/
theorem topTruncationRaw_support (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ∀ j : ℤ, j < K.property.choose ∨ topCutoff K - 1 < j →
      IsZero ((topTruncationRaw F hKernelClosure K hK).X j) :=
  TruncationAt.topTruncationRaw_support (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw kernel truncation T is bounded with the inherited lower bound and upper bound t−1. -/
theorem bounded_topTruncationRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CochainComplex.bounded E (topTruncationRaw F hKernelClosure K hK) :=
  TruncationAt.bounded_topTruncationRaw (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw cochain kernel T, with its proved finite support, is an object of Bounded(E). -/
abbrev topTruncation (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : Bounded E :=
  TruncationAt.topTruncation (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure) (a :=
    K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The kernel inclusion i:T → K is the corresponding bounded cochain morphism. -/
abbrev topTruncationι (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncation F hKernelClosure K hK ⟶ K :=
  TruncationAt.topTruncationι (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure) (a :=
    K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The underlying map of the bounded truncation inclusion is the raw cochain kernel inclusion i. -/
theorem topTruncationι_hom (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationι F hKernelClosure K hK).hom = topTruncationRawι F hKernelClosure K hK :=
  TruncationAt.topTruncationι_hom (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure)
    (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The bounded inclusion followed by the bounded disk projection is zero. -/
theorem topTruncationι_projection (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationι F hKernelClosure K hK ≫ topDiskProjectionBounded K = 0 :=
  TruncationAt.topTruncationι_projection (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw truncation short complex is T —i→ K —π→ D_t. -/
abbrev topTruncationRawShortComplex (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ShortComplex (CochainComplex E ℤ) :=
  TruncationAt.topTruncationRawShortComplex (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Every term row T^j → K^j → D_t^j is admissible exact in E. -/
theorem topTruncationRawShortComplex_term_isAdmissibleExact (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleExact ((topTruncationRawShortComplex F hKernelClosure K hK).map
      (HomologicalComplex.eval E (.up ℤ) j)) :=
  TruncationAt.topTruncationRawShortComplex_term_isAdmissibleExact (b := topCutoff K) (F := F)
    (hKernelClosure := hKernelClosure) (a := K.property.choose) (hSupport :=
    K.property.choose_spec.choose_spec) (K := K) (hK := hK) (j := j)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Every component of the bounded inclusion i:T → K is an admissible monomorphism. -/
theorem topTruncationι_isAdmissibleMono_f (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) (j : ℤ) :
    IsAdmissibleMono ((topTruncationι F hKernelClosure K hK).hom.f j) :=
  TruncationAt.topTruncationι_isAdmissibleMono_f (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (j := j)

variable [F.IsExact]

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K. Assume also F is exact.

The mapped raw row 0 → F(T) → F(K) → F(D_t) → 0 is short exact in ambient cochain complexes. -/
theorem topTruncationRawShortComplex_map_shortExact (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((topTruncationRawShortComplex F hKernelClosure K hK).map
      (F.mapHomologicalComplex (.up ℤ))).ShortExact :=
  TruncationAt.topTruncationRawShortComplex_map_shortExact (b := topCutoff K) (F := F)
    (hKernelClosure := hKernelClosure) (a := K.property.choose) (hSupport :=
    K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K. Assume also F is exact.

The truncated complex F(T) is acyclic in the ambient category. -/
theorem topTruncation_map_acyclic (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
      (topTruncation F hKernelClosure K hK).obj).Acyclic :=
  TruncationAt.topTruncation_map_acyclic (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw truncation cofiber is the homotopy cofiber Cofib(i) of the raw inclusion. -/
abbrev topTruncationCofiberRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : CochainComplex E ℤ :=
  TruncationAt.topTruncationCofiberRaw (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw cofiber Cofib(i) is bounded, using the finite support of T and K with the source shift by one. -/
theorem bounded_topTruncationCofiberRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CochainComplex.bounded E (topTruncationCofiberRaw F hKernelClosure K hK) :=
  TruncationAt.bounded_topTruncationCofiberRaw (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The homotopy cofiber Cofib(i), with its proved support, is the bounded truncation-cofiber object. -/
abbrev topTruncationCofiber (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) : Bounded E :=
  TruncationAt.topTruncationCofiber (b := topCutoff K) (F := F) (hKernelClosure := hKernelClosure)
    (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The descendant r:Cofib(i) → D_t is induced by π and the zero composite π∘i. -/
abbrev topTruncationCofiberDescRaw (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationCofiberRaw F hKernelClosure K hK ⟶ topDiskRaw K :=
  TruncationAt.topTruncationCofiberDescRaw (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The target inclusion K → Cofib(i) followed by r equals π. -/
theorem topTruncationCofiber_inr_desc (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    HomologicalComplex.homotopyCofiber.inr (topTruncationRawι F hKernelClosure K hK) ≫
      topTruncationCofiberDescRaw F hKernelClosure K hK = topDiskProjection K :=
  TruncationAt.topTruncationCofiber_inr_desc (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Each shifted-source component of r:Cofib(i) → D_t is zero, from its defining zero homotopy. -/
theorem topTruncationCofiber_inlX_desc_f (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    HomologicalComplex.homotopyCofiber.inlX (topTruncationRawι F hKernelClosure K hK) j i hij ≫
      (topTruncationCofiberDescRaw F hKernelClosure K hK).f i = 0 :=
  TruncationAt.topTruncationCofiber_inlX_desc_f (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK) (i := i) (j := j) (hij := hij)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The raw descendant r is the corresponding bounded morphism Cofib(i) → D_t. -/
abbrev topTruncationCofiberDesc (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    topTruncationCofiber F hKernelClosure K hK ⟶ topDisk K :=
  TruncationAt.topTruncationCofiberDesc (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Forgetting boundedness from the descendant returns the raw map r. -/
theorem topTruncationCofiberDesc_hom (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationCofiberDesc F hKernelClosure K hK).hom =
      topTruncationCofiberDescRaw F hKernelClosure K hK :=
  TruncationAt.topTruncationCofiberDesc_hom (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

The additive-functor comparison F(Cofib(i)) ≅ Cofib(F(i)) identifies the two cofiber constructions. -/
abbrev topTruncationCofiberMapIso (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (F.mapHomologicalComplex (.up ℤ)).obj (topTruncationCofiberRaw F hKernelClosure K hK) ≅
      HomologicalComplex.homotopyCofiber
        ((F.mapHomologicalComplex (.up ℤ)).map (topTruncationRawι F hKernelClosure K hK)) :=
  TruncationAt.topTruncationCofiberMapIso (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

omit [F.IsExact] in
/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K.

Under F(Cofib(i)) ≅ Cofib(F(i)), the mapped descendant F(r) equals the canonical descendant of the mapped row F(T) → F(K) → F(D_t). -/
theorem topTruncationCofiberDesc_map (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (topTruncationCofiberMapIso F hKernelClosure K hK).hom ≫
      HomologicalComplex.homotopyCofiber.descShortComplex
        ((topTruncationRawShortComplex F hKernelClosure K hK).map
          (F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map (topTruncationCofiberDescRaw F hKernelClosure K hK) :=
  TruncationAt.topTruncationCofiberDesc_map (b := topCutoff K) (F := F) (hKernelClosure :=
    hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec) (K
    := K) (hK := hK)

/-- Let E be preadditive with a zero object and binary biproducts,
and K a bounded integer cochain complex. t is the selected upper endpoint of K’s support witness.
Let S_t be the single complex on K^t, D_t=Cofib(1_{S_t}),
and ℓ:K^t ≅ D_t^{t−1}, u:K^t ≅ D_t^t the lower and upper charts. Assume E is Quillen exact and F:E → A is additive fully faithful,
with A abelian. Assume F reflects admissible exactness, its essential image
is closed under kernels of epimorphisms between image objects, and F(K)
is acyclic. Let [a,t] be the selected support interval of K.
Write π:K → D_t for the top-disk projection, T=Ker(π) and i:T → K. Assume also F is exact.

The image under F of the bounded descendant r:Cofib(i) → D_t is a quasi-isomorphism. -/
theorem topTruncationCofiberDesc_map_quasiIso (K : Bounded E)
    (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (topTruncationCofiberDesc F hKernelClosure K hK).hom) :=
  TruncationAt.topTruncationCofiberDesc_map_quasiIso (b := topCutoff K) (F := F) (hKernelClosure
    := hKernelClosure) (a := K.property.choose) (hSupport := K.property.choose_spec.choose_spec)
    (K := K) (hK := hK)

end CochainComplex.Bounded

end
