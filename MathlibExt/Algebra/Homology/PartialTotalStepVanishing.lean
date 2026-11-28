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

public import MathlibExt.Algebra.Homology.PartialTotalStepHomology

/-!
# Homology and support of partial-total filtration-step cones

Let B be a bicomplex of shape (down ℕ,down ℕ) in an abelian category. Write P_p for its partial
total through horizontal column p, with P_{-1}=0. The pth step is the short exact sequence
P_{p-1}→P_p→R_p, where R_p places B_{p,q} in total degree p+q and has vertical differential
(-1)^p d. Extend chain degree k to cochain degree -k.

The cone of the extended step inclusion has homology isomorphic to that of the extended signed
row R_p in every integer cochain degree. Since R_p is supported in chain degrees at least p, the
cone homology vanishes in cochain degree -k for k∈ℕ with k<p. Category object and morphism
universes are arbitrary.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- Let C be abelian and B a bicomplex of shape (down ℕ,down ℕ). For p∈ℕ, let P_{p-1}→P_p→R_p be the
partial-total step, with P_{-1}=0 and R_p the pth row placed in degree p+q with differential
(-1)^p d. After extending chain degree k to cochain degree -k, let a_p be the step inclusion.
For every n∈ℤ this is the canonical isomorphism H^n(Cone(a_p))≅H^n(E R_p), induced by the cone
map to the short-exact quotient and its row identification. -/
noncomputable def partialTotalStepConeExtendedRowHomologyIso (p : ℕ) (n : ℤ) :
    (CochainComplex.mappingCone
        (B.partialTotalStepCochainShortComplex p).f).homology n ≅
      ((B.totalRow p).extend ComplexShape.embeddingDownNat).homology n := by
  let S := B.partialTotalStepCochainShortComplex p
  let hS : S.ShortExact := B.partialTotalStepCochainShortExact p
  let desc := CochainComplex.mappingCone.descShortComplex S
  let _ : QuasiIso desc :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  exact asIso (HomologicalComplex.homologyMap desc n) ≪≫
    HomologicalComplex.homologyMapIso (B.partialTotalStepCochainX₃Iso p) n

/-- For a first-quadrant bicomplex B in an abelian category and p,k∈ℕ with k<p, let a_p be the
inclusion P_{p-1}→P_p extended from chain degree r to cochain degree -r, using P_{-1}=0. Then
H^{-k}(Cone(a_p)) is zero. Its comparison with the extended signed row R_p identifies it with
H_k(R_p), and R_p has no terms in total degrees below p. -/
theorem isZero_partialTotalStepConeHomology_of_lt
    (p k : ℕ) (h : k < p) :
    IsZero ((CochainComplex.mappingCone
      (B.partialTotalStepCochainShortComplex p).f).homology (-(k : ℤ))) := by
  have hRow : IsZero ((B.totalRow p).homology k) :=
    ((B.totalRow p).sc k).isZero_homology_of_isZero_X₂
      (B.totalRow_isZero_X p k h)
  have hExtended : IsZero
      (((B.totalRow p).extend ComplexShape.embeddingDownNat).homology
        (-(k : ℤ))) :=
    IsZero.of_iso hRow
      ((B.totalRow p).extendHomologyIso
        ComplexShape.embeddingDownNat rfl)
  exact IsZero.of_iso hExtended
    (B.partialTotalStepConeExtendedRowHomologyIso p (-(k : ℤ)))

end HomologicalComplex₂

end
