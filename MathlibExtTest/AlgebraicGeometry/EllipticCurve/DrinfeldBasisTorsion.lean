/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.DrinfeldBasisTorsion
public import MathlibExtTest.AlgebraicGeometry.DrinfeldBasis

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace DrinfeldBasisTorsionTest

/-- Consumer with the original binders: a field `K` in `Type`, a Weierstrass curve with
unit discriminant, a prime level, and a separated structure morphism in place of the
projective model of the curve. -/
theorem exactSource {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve.Projective K)
    (_hΔ : IsUnit W.Δ) {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)} [IsSeparated f]
    (G : RelativeGroupLaw K f)
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) f ≃
        (W.baseChange F).toAffine.Point)
    (hev : DrinfeldGlobal.IsAdditivePointsEval W G ev)
    (q : ℕ) [Fact q.Prime]
    (hss : ∀ R : W.toAffine.Point, q • R = 0 → R = 0)
    (P Q : DrinfeldGlobal.Section f) (hPQ : DrinfeldGlobal.IsDrinfeldBasis G q P Q) :
    P = G.one (𝟙 _) ∧ Q = G.one (𝟙 _) :=
  DrinfeldGlobal.IsDrinfeldBasis.eq_one_of_forall_nsmul_eq_zero hev
    (Fact.out : q.Prime).two_le hss hPQ

/-- The same consumer in a higher universe. -/
theorem exactSource_univ1 {K : Type 1} [Field K] [DecidableEq K]
    (W : WeierstrassCurve.Projective K) {A : Scheme.{1}} {f : A ⟶ Spec (CommRingCat.of K)}
    [IsSeparated f] (G : RelativeGroupLaw K f)
    (ev : ∀ (F : Type 1) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) f ≃
        (W.baseChange F).toAffine.Point)
    (hev : DrinfeldGlobal.IsAdditivePointsEval W G ev)
    (q : ℕ) [Fact q.Prime]
    (hss : ∀ R : W.toAffine.Point, q • R = 0 → R = 0)
    (P Q : DrinfeldGlobal.Section f) (hPQ : DrinfeldGlobal.IsDrinfeldBasis G q P Q) :
    P = G.one (𝟙 _) ∧ Q = G.one (𝟙 _) :=
  DrinfeldGlobal.IsDrinfeldBasis.eq_one_of_forall_nsmul_eq_zero hev
    (Fact.out : q.Prime).two_le hss hPQ

section Boundaries

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f)

/-- At level one a section is torsion only when it is the unit section. -/
theorem isTorsionPoint_one_iff (P : DrinfeldGlobal.Section f) :
    G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) 1 P ↔
      P = G.one (𝟙 (Spec (CommRingCat.of R))) := by
  rw [RelativeGroupLaw.isTorsionPoint_def, RelativeGroupLaw.nsmul_one]

/-- The hypothesis `2 ≤ q` matters: every pair is a Drinfeld basis at level one, so the
torsion conclusion at level one would force every section to be the unit section. -/
theorem eq_one_of_isTorsionPoint_levelOne
    (h : ∀ P Q : DrinfeldGlobal.Section f, DrinfeldGlobal.IsDrinfeldBasis G 1 P Q →
      G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) 1 P)
    (P : DrinfeldGlobal.Section f) : P = G.one (𝟙 (Spec (CommRingCat.of R))) :=
  (isTorsionPoint_one_iff G P).mp (h P P (DrinfeldBasisTest.isDrinfeldBasis_one G P P))

/-- At level two a Drinfeld basis of a separated law is a valid one. -/
example [IsSeparated f] (P Q : DrinfeldGlobal.Section f)
    (h : DrinfeldGlobal.IsDrinfeldBasis G 2 P Q) :
    DrinfeldGlobal.IsValidDrinfeldBasis G 2 P Q :=
  (DrinfeldGlobal.isValidDrinfeldBasis_iff_isDrinfeldBasis G le_rfl P Q).mpr h

end Boundaries

end DrinfeldBasisTorsionTest
