/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.HomologicalComplexCokernelHomology
public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveCokernel

/-!
# Homology in degrees zero and one of the both-positive quotient

For a pairing of nonnegative chain complexes with both first differentials
zero, the strict-positive source has zero degree-zero and degree-one terms.
Its map into K₃ therefore vanishes in degrees n<2.

In an abelian monoidal category with additive tensoring, the cokernel
projection preserves H_n for n<2. In a module category with chosen tensor,
the pointwise positive image quotient has the same comparison through
its canonical cokernel isomorphism. No higher-degree assertion is needed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

section GeneralNativeCokernel

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {K₁ K₂ K₃ : ChainComplex C ℕ} (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- Let C be an abelian monoidal category with additive tensoring.
Let P:K₁⊗K₂→K₃ be a graded pairing of nonnegative chain complexes
with K₁.d(1,0)=K₂.d(1,0)=0.
Write P₊₊:K₁,≥1⊗K₂,≥1→K₃ for the strict-positive map.
For n<2, the degree n component of P₊₊ is zero because
no two positive bidegrees sum to n. -/
theorem strictPositivePairing_f_eq_zero (n : ℕ) (hn : n < 2) :
    (strictPositivePairing P h₁ h₂).f n = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  subst n
  simp only [comp_zero]
  change (strictPositivePairing P h₁ h₂).pair p q = 0
  have hcompat : tensorHom (K₁.positiveStupidTruncInclusion h₁)
      (K₂.positiveStupidTruncInclusion h₂) ≫ P =
        strictPositivePairing P h₁ h₂ ≫ 𝟙 K₃ := by
    simp only [strictPositivePairing, Category.comp_id]
  have h := pair_naturality (strictPositivePairing P h₁ h₂) P
    (K₁.positiveStupidTruncInclusion h₁)
    (K₂.positiveStupidTruncInclusion h₂) (𝟙 K₃) hcompat p q
  have hzero : p = 0 ∨ q = 0 := by omega
  rcases hzero with hp | hq
  · subst p
    rw [positiveStupidTruncInclusion_f_zero] at h
    simpa only [MonoidalPreadditive.zero_tensor, zero_comp, id_f,
      Category.comp_id] using h.symm
  · subst q
    rw [positiveStupidTruncInclusion_f_zero] at h
    simpa only [MonoidalPreadditive.tensor_zero, zero_comp, id_f,
      Category.comp_id] using h.symm

/-- Let C be an abelian monoidal category with additive tensoring.
Let P:K₁⊗K₂→K₃ be a graded pairing of nonnegative chain complexes
with K₁.d(1,0)=K₂.d(1,0)=0.
Write P₊₊:K₁,≥1⊗K₂,≥1→K₃ for the strict-positive map.
For n<2, the cokernel projection K₃→Coker(P₊₊) is
a quasi-isomorphism in degree n. -/
theorem strictPositiveProjection_quasiIsoAt (n : ℕ) (hn : n < 2) :
    QuasiIsoAt (strictPositiveProjection P h₁ h₂) n := by
  change QuasiIsoAt (cokernel.π (strictPositivePairing P h₁ h₂)) n
  apply HomologicalComplex.quasiIsoAt_cokernelProjection_of_zero_components
  · exact strictPositivePairing_f_eq_zero P h₁ h₂ n hn
  · apply strictPositivePairing_f_eq_zero P h₁ h₂
    have hnext : (ComplexShape.down ℕ).next n ≤ n := by
      cases n <;> simp
    omega

/-- Let C be an abelian monoidal category with additive tensoring.
Let P:K₁⊗K₂→K₃ be a graded pairing of nonnegative chain complexes
with K₁.d(1,0)=K₂.d(1,0)=0.
Write P₊₊:K₁,≥1⊗K₂,≥1→K₃ for the strict-positive map.
For n<2, the projection gives
H_n(K₃)≅H_n(Coker(P₊₊)). -/
def strictPositiveCokernelHomologyIso (n : ℕ) (hn : n < 2) :
    K₃.homology n ≅ (strictPositiveCokernel P h₁ h₂).homology n := by
  letI := strictPositiveProjection_quasiIsoAt P h₁ h₂ n hn
  exact _root_.isoOfQuasiIsoAt (strictPositiveProjection P h₁ h₂) n

/-- Let C be an abelian monoidal category with additive tensoring.
Let P:K₁⊗K₂→K₃ be a graded pairing of nonnegative chain complexes
with K₁.d(1,0)=K₂.d(1,0)=0.
Write P₊₊:K₁,≥1⊗K₂,≥1→K₃ for the strict-positive map.
The forward low homology comparison is H_n(π_coker)
for n<2. -/
theorem strictPositiveCokernelHomologyIso_hom (n : ℕ) (hn : n < 2) :
    (strictPositiveCokernelHomologyIso P h₁ h₂ n hn).hom =
      HomologicalComplex.homologyMap (strictPositiveProjection P h₁ h₂) n := rfl

end GeneralNativeCokernel

section ModulePointwiseQuotient

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃)
  (h₁ : K₁.d 1 0 = 0) (h₂ : K₂.d 1 0 = 0)

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
For n<2, the pointwise positive image projection is a
quasi-isomorphism in degree n. -/
theorem positiveImageProjection_quasiIsoAt (n : ℕ) (hn : n < 2) :
    QuasiIsoAt (positiveImageProjection P h₁ h₂) n := by
  let := strictPositiveProjection_quasiIsoAt P h₁ h₂ n hn
  let e := strictPositiveCokernelIsoPositiveImageQuotient P h₁ h₂
  have h : QuasiIsoAt (strictPositiveProjection P h₁ h₂ ≫ e.hom) n := by
    infer_instance
  simpa only [e, strictPositiveProjection_comp_iso_hom] using h

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
For n<2, the image quotient projection gives
H_n(K₃)≅H_n(Q_J). -/
def positiveImageQuotientHomologyIso (n : ℕ) (hn : n < 2) :
    K₃.homology n ≅ (positiveImageQuotient P h₁ h₂).homology n := by
  letI := positiveImageProjection_quasiIsoAt P h₁ h₂ n hn
  exact _root_.isoOfQuasiIsoAt (positiveImageProjection P h₁ h₂) n

/-- Let R be a ring in universe u and ModuleCat_v R have a chosen
monoidal preadditive structure. Let P be a chain pairing with both
first differentials zero. Its strict-positive map P₊₊ has bidegrees
p,q>0, and J_n=∑_(p,q>0,p+q=n)range(P_(p,q)).
For n<2, the forward image quotient homology isomorphism
is H_n(π_J). -/
theorem positiveImageQuotientHomologyIso_hom (n : ℕ) (hn : n < 2) :
    (positiveImageQuotientHomologyIso P h₁ h₂ n hn).hom =
      HomologicalComplex.homologyMap (positiveImageProjection P h₁ h₂) n := rfl

end ModulePointwiseQuotient

end HomologicalComplex.ChainGradedPairing
