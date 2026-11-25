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
projective model of the curve. The points evaluation is assumed only to be additive
(`IsAdditivePointsEval`), the first half of the source's points-evaluation hypothesis. -/
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
    (W : WeierstrassCurve.Projective K) (_hΔ : IsUnit W.Δ) {A : Scheme.{1}}
    {f : A ⟶ Spec (CommRingCat.of K)} [IsSeparated f] (G : RelativeGroupLaw K f)
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

/-- At a prime level both sections of a Drinfeld basis of a separated law over a
commutative ring are killed by multiplication by the level. -/
theorem nsmul_eq_one_of_isDrinfeldBasis {T : Type} [CommRing T] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of T)} [IsSeparated f] (G : RelativeGroupLaw T f)
    (q : ℕ) [Fact q.Prime] (P Q : DrinfeldGlobal.Section f)
    (h : DrinfeldGlobal.IsDrinfeldBasis G q P Q) :
    G.nsmul (𝟙 (Spec (CommRingCat.of T))) q P = G.one (𝟙 (Spec (CommRingCat.of T))) ∧
      G.nsmul (𝟙 (Spec (CommRingCat.of T))) q Q = G.one (𝟙 (Spec (CommRingCat.of T))) :=
  h.isTorsionPoint (Fact.out : q.Prime).two_le

section PointsEval

variable {K : Type u} [Field K] {W : WeierstrassCurve.Projective K} {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of K)} {G : RelativeGroupLaw K f}
  {ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra K F],
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) f ≃
      (W.baseChange F).toAffine.Point}

/-- An additive points evaluation sends the unit point over each field `F` over `K` to the
zero point. -/
private theorem ev_one_of_isAdditivePointsEval (hev : DrinfeldGlobal.IsAdditivePointsEval W G ev)
    (F : Type u) [Field F] [DecidableEq F] [Algebra K F] :
    ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap K F)))) = 0 := by
  have h := hev F (G.one _) (G.one _)
  rw [G.one_mul] at h
  exact add_eq_left.mp h.symm

/-- An additive points evaluation sends the `n`-th multiple of a point to the `n`-th
multiple of its image. -/
example (hev : DrinfeldGlobal.IsAdditivePointsEval W G ev) (F : Type u) [Field F]
    [DecidableEq F] [Algebra K F] (n : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) f) :
    ev F (G.nsmul _ n x) = n • ev F x := by
  induction n with
  | zero => rw [G.nsmul_zero, zero_smul]; exact ev_one_of_isAdditivePointsEval hev F
  | succ n ih => rw [G.nsmul_succ, hev, ih, succ_nsmul]

end PointsEval

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

section TrivialLaw

/-- Over a test scheme the base has exactly one point over itself. -/
private theorem hom_ext_base {R : Type u} [CommRing R] {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    (x y : Over.mk t ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R)))) : x = y :=
  Over.OverMorphism.ext (by simpa using (Over.w x).trans (Over.w y).symm)

/-- The trivial relative group law on the base over itself. -/
private noncomputable def trivialLaw (R : Type u) [CommRing R] :
    RelativeGroupLaw R (𝟙 (Spec (CommRingCat.of R))) where
  mul _ x _ := x
  one t := Over.homMk t (Category.comp_id t)
  inv _ x := x
  mul_assoc _ _ _ _ := rfl
  one_mul _ _ := hom_ext_base _ _
  mul_one _ _ := rfl
  inv_mul_cancel _ _ := hom_ext_base _ _
  mul_natural _ _ _ _ _ _ := rfl

/-- On the trivial law the graphs of the basis tuple and the torsion morphism are
isomorphisms, so the basis divisor and the torsion ideal are both zero: every pair of
sections is a Drinfeld basis at level two. -/
private theorem isDrinfeldBasis_trivialLaw (R : Type u) [CommRing R]
    (P Q : DrinfeldGlobal.Section (𝟙 (Spec (CommRingCat.of R)))) :
    DrinfeldGlobal.IsDrinfeldBasis (trivialLaw R) 2 P Q := by
  have hgraph (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
      (ha : a ≫ 𝟙 (Spec (CommRingCat.of R)) = 𝟙 (Spec (CommRingCat.of R))) :
      (graphOver (𝟙 (Spec (CommRingCat.of R))) a ha).ker = ⊥ := by
    obtain rfl : a = 𝟙 _ := by simpa using ha
    have : IsIso (graphOver (𝟙 (Spec (CommRingCat.of R))) (𝟙 _) ha ≫
        pullback.fst (𝟙 (Spec (CommRingCat.of R))) (𝟙 (Spec (CommRingCat.of R)))) := by
      rw [graphOver_fst]
      infer_instance
    have := IsIso.of_isIso_comp_right (graphOver (𝟙 (Spec (CommRingCat.of R))) (𝟙 _) ha)
      (pullback.fst (𝟙 (Spec (CommRingCat.of R))) (𝟙 (Spec (CommRingCat.of R))))
    exact Scheme.Hom.ker_eq_bot_of_isIso _
  have hid : DrinfeldGlobal.toPullbackId (f := 𝟙 (Spec (CommRingCat.of R))) ≫
      pullback.fst (𝟙 (Spec (CommRingCat.of R))) (𝟙 (Spec (CommRingCat.of R))) =
        𝟙 (Spec (CommRingCat.of R)) :=
    pullback.lift_fst _ _ _
  have : IsIso (DrinfeldGlobal.toPullbackId (f := 𝟙 (Spec (CommRingCat.of R))) ≫
      pullback.fst (𝟙 (Spec (CommRingCat.of R))) (𝟙 (Spec (CommRingCat.of R)))) := by
    rw [hid]
    infer_instance
  have := IsIso.of_isIso_comp_right (DrinfeldGlobal.toPullbackId (f := 𝟙 (Spec (CommRingCat.of R))))
    (pullback.fst (𝟙 (Spec (CommRingCat.of R))) (𝟙 (Spec (CommRingCat.of R))))
  have : IsIso ((trivialLaw R).one (𝟙 (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsIso (𝟙 _))
  unfold DrinfeldGlobal.IsDrinfeldBasis DrinfeldGlobal.basisDivisor prodKerGraph
    DrinfeldGlobal.torsionIdeal
  rw [Scheme.Hom.ker_eq_bot_of_isIso]
  exact Finset.prod_eq_zero (i := ⟨0, by norm_num⟩) (Finset.mem_univ _) (hgraph _ _)

/-- A concrete Drinfeld basis: on the trivial law every pair of sections is one at level
two, so `isValidDrinfeldBasis_iff_isDrinfeldBasis` and `IsDrinfeldBasis.isTorsionPoint`
apply with all of their hypotheses met. -/
example (R : Type u) [CommRing R] (P Q : DrinfeldGlobal.Section (𝟙 (Spec (CommRingCat.of R)))) :
    DrinfeldGlobal.IsValidDrinfeldBasis (trivialLaw R) 2 P Q :=
  (DrinfeldGlobal.isValidDrinfeldBasis_iff_isDrinfeldBasis _ le_rfl P Q).mpr
    (isDrinfeldBasis_trivialLaw R P Q)

end TrivialLaw

end DrinfeldBasisTorsionTest
