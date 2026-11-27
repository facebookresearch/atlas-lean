/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_eq_one_of_forall_nsmul_eq_zero.lean`,
and the solution files for that theorem and for
`Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_
exists_comp_fst_schemeKer_eq.lean`
in `P2M/Sol/`

(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import MathlibExt.AlgebraicGeometry.DrinfeldBasis

/-!
# Sections of a Drinfeld basis are torsion

For a relative group law `G` on a separated `f : A ⟶ Spec R` and a level `q ≥ 2`, the
basis tuple of a Drinfeld basis `(P, Q)` contains `P` and `Q`. Since the basis divisor is the
torsion ideal, the graphs of `P` and `Q` factor through the kernel of multiplication by
`q`, so both sections are `q`-torsion.

Over a field `K`, suppose that a family of additive identifications, one for every field
`F` over `K`, matches the points of `G` over `F` with the `F`-points of a Weierstrass curve
`W`, and that `W` has no nonzero `q`-torsion `K`-point. Then any Drinfeld basis at level
`q ≥ 2` consists of the unit sections.

## Main results

* `AlgebraicGeometry.DrinfeldGlobal.IsDrinfeldBasis.isTorsionPoint`: both sections of a
  Drinfeld basis at level `q ≥ 2` are `q`-torsion.
* `AlgebraicGeometry.DrinfeldGlobal.isValidDrinfeldBasis_iff_isDrinfeldBasis`: at level
  `q ≥ 2` a Drinfeld basis is automatically a valid one.
* `AlgebraicGeometry.DrinfeldGlobal.IsDrinfeldBasis.eq_one_of_forall_nsmul_eq_zero`: with no
  nontrivial `q`-torsion points, a Drinfeld basis consists of the unit sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace DrinfeldGlobal

private theorem prodKerGraph_le {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) {g : T ⟶ S} {r : ℕ}
    (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) (i : Fin r) :
    prodKerGraph f a ha ≤ (graphOver f (a i) (ha i)).ker := by
  rw [prodKerGraph_eq_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    Scheme.IdealSheafData.le_def]
  intro U
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  exact Ideal.mul_le_left

section Ring

variable {R : Type u} [CommRing R] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

private theorem toPullbackId_fst :
    toPullbackId (f := f) ≫ pullback.fst f (𝟙 (Spec (CommRingCat.of R))) = 𝟙 A :=
  pullback.lift_fst _ _ _

private theorem isIso_toPullbackId : IsIso (toPullbackId (f := f)) := by
  have : IsIso (toPullbackId (f := f) ≫ pullback.fst f (𝟙 (Spec (CommRingCat.of R)))) := by
    rw [toPullbackId_fst]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (pullback.fst f (𝟙 (Spec (CommRingCat.of R))))

private theorem isClosedImmersion_one [IsSeparated f] :
    IsClosedImmersion (G.one (𝟙 (Spec (CommRingCat.of R)))).left := by
  have hone : (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ f =
      𝟙 (Spec (CommRingCat.of R)) :=
    Over.w (G.one (𝟙 (Spec (CommRingCat.of R))))
  have : IsClosedImmersion ((G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ f) := by
    rw [hone]
    exact inferInstanceAs (IsClosedImmersion (𝟙 (Spec (CommRingCat.of R))))
  exact IsClosedImmersion.of_comp _ f

/-- A section that occurs in the basis tuple of a Drinfeld basis is `q`-torsion. -/
private theorem isTorsionPoint_of_basisTuple_eq [IsSeparated f] {q : ℕ} {P Q X : Section f}
    (h : IsDrinfeldBasis G q P Q) (i : Fin (q * q)) (hi : basisTuple G q P Q i = X.left) :
    G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) q X := by
  have hone : (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ f =
      𝟙 (Spec (CommRingCat.of R)) :=
    Over.w (G.one (𝟙 (Spec (CommRingCat.of R))))
  have := isClosedImmersion_one G
  have := isIso_toPullbackId (f := f)
  set e := (G.one (𝟙 (Spec (CommRingCat.of R)))).left with he
  set a := basisTuple G q P Q i
  have ha : a ≫ f = 𝟙 (Spec (CommRingCat.of R)) := basisTuple_over G q P Q i
  set k := pullback.fst (G.schemeNsmul q) e ≫ toPullbackId (f := f)
  have hle : k.ker ≤ (graphOver f a ha).ker :=
    (le_of_eq h.symm).trans (prodKerGraph_le f (basisTuple G q P Q) (basisTuple_over G q P Q) i)
  set p := IsClosedImmersion.lift k (graphOver f a ha) hle
  have hp : p ≫ k = graphOver f a ha := IsClosedImmersion.lift_fac k _ hle
  have hfst : p ≫ pullback.fst (G.schemeNsmul q) e = a := by
    have := congrArg (· ≫ pullback.fst f (𝟙 (Spec (CommRingCat.of R)))) hp
    simpa only [k, Category.assoc, toPullbackId_fst, Category.comp_id, graphOver_fst] using this
  have hsnd : p ≫ pullback.snd (G.schemeNsmul q) e = 𝟙 (Spec (CommRingCat.of R)) := by
    calc p ≫ pullback.snd (G.schemeNsmul q) e
        = p ≫ pullback.snd (G.schemeNsmul q) e ≫ e ≫ f := by rw [hone]; simp
      _ = p ≫ pullback.fst (G.schemeNsmul q) e ≫ G.schemeNsmul q ≫ f := by
          rw [← Category.assoc (pullback.snd _ _), ← pullback.condition, Category.assoc]
      _ = a ≫ f := by rw [G.schemeNsmul_comp, ← Category.assoc, hfst]
      _ = 𝟙 (Spec (CommRingCat.of R)) := ha
  rw [RelativeGroupLaw.isTorsionPoint_def, ← G.comp_nsmul_idPoint]
  ext
  change X.left ≫ G.schemeNsmul q = e
  rw [← hi, ← hfst, Category.assoc, pullback.condition, ← Category.assoc, hsnd]
  simp

variable {G} in
/-- At a level `q ≥ 2`, both sections of a Drinfeld basis of a relative group law on a
separated `f` are `q`-torsion: the basis tuple contains `P` and `Q`, and the torsion ideal
is contained in the ideal of each graph in the tuple. -/
theorem IsDrinfeldBasis.isTorsionPoint [IsSeparated f] {q : ℕ} (hq : 2 ≤ q)
    {P Q : Section f} (h : IsDrinfeldBasis G q P Q) :
    G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) q P ∧
      G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) q Q := by
  have hq0 : 0 < q := by omega
  have hq1 : 1 < q := by omega
  have hqq : q < q * q := by nlinarith
  refine ⟨isTorsionPoint_of_basisTuple_eq G h ⟨q, hqq⟩ ?_,
    isTorsionPoint_of_basisTuple_eq G h ⟨1, lt_trans hq1 hqq⟩ ?_⟩
  · change (linComb G P Q (q / q) (q % q)).left = P.left
    rw [Nat.div_self hq0, Nat.mod_self, linComb, G.nsmul_one, G.nsmul_zero, G.mul_one]
  · change (linComb G P Q (1 / q) (1 % q)).left = Q.left
    rw [Nat.div_eq_of_lt hq1, Nat.mod_eq_of_lt hq1, linComb, G.nsmul_one, G.nsmul_zero,
      G.one_mul]

/-- For a relative group law on a separated `f` and a level `q ≥ 2`, `IsValidDrinfeldBasis`
is equivalent to `IsDrinfeldBasis`: its positivity and torsion conditions follow from
`IsDrinfeldBasis`. -/
theorem isValidDrinfeldBasis_iff_isDrinfeldBasis [IsSeparated f] {q : ℕ} (hq : 2 ≤ q)
    (P Q : Section f) : IsValidDrinfeldBasis G q P Q ↔ IsDrinfeldBasis G q P Q :=
  ⟨fun h => h.isDrinfeldBasis, fun h =>
    ⟨by omega, (h.isTorsionPoint hq).1, (h.isTorsionPoint hq).2, h⟩⟩

end Ring

/-- A family of identifications of the sections of `f` over fields `F` with the points
of a Weierstrass curve over `F` is additive when it sends the relative group law to
addition of points. -/
def IsAdditivePointsEval {K : Type u} [Field K] (W : WeierstrassCurve.Projective K)
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f)
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) f ≃
        (W.baseChange F).toAffine.Point) : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra K F]
    (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) f),
    ev F (G.mul _ P Q) = ev F P + ev F Q

section Field

variable {K : Type u} [Field K] [DecidableEq K] {W : WeierstrassCurve.Projective K}
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} {G : RelativeGroupLaw K f}
  {ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra K F],
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) f ≃
      (W.baseChange F).toAffine.Point}

private theorem ev_one (hev : IsAdditivePointsEval W G ev) :
    ev K (G.one (Spec.map (CommRingCat.ofHom (algebraMap K K)))) = 0 := by
  have h := hev K (G.one _) (G.one _)
  rw [G.one_mul] at h
  exact (add_eq_left.mp h.symm)

private theorem ev_nsmul (hev : IsAdditivePointsEval W G ev) (n : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K))) f) :
    ev K (G.nsmul _ n x) = n • ev K x := by
  induction n with
  | zero => rw [G.nsmul_zero, zero_smul]; exact ev_one hev
  | succ n ih => rw [G.nsmul_succ, hev, ih, succ_nsmul]

omit [DecidableEq K] in
private theorem id_comp_id_eq_specMap :
    (𝟙 (Spec (CommRingCat.of K)) ≫ 𝟙 (Spec (CommRingCat.of K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K K)) := by
  rw [Category.comp_id, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

private theorem eq_one_of_isTorsionPoint (hev : IsAdditivePointsEval W G ev) {q : ℕ}
    (hss : ∀ R : W.toAffine.Point, q • R = 0 → R = 0) {P : Section f}
    (hP : G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) q P) :
    P = G.one (𝟙 (Spec (CommRingCat.of K))) := by
  set ι := Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K))))
    (V := Over.mk (𝟙 (Spec (CommRingCat.of K)))) (𝟙 _) id_comp_id_eq_specMap
  have htors : G.nsmul _ q (ι ≫ P) = G.one _ := by
    rw [← G.homMk_comp_nsmul, (G.isTorsionPoint_def _ _ _).mp hP, G.one_natural]
  have hq0 : q • ev K (ι ≫ P) = 0 := by rw [← ev_nsmul hev, htors, ev_one hev]
  have hss' : ∀ R : (W.baseChange K).toAffine.Point, q • R = 0 → R = 0 := hss
  have h1 : ι ≫ P = G.one _ :=
    (ev K).injective (by rw [hss' _ hq0, ev_one hev])
  rw [← G.one_natural (𝟙 _) _ (𝟙 _) id_comp_id_eq_specMap] at h1
  ext
  simpa [ι] using congrArg (fun x => x.left) h1

/-- Over a field `K`, let `G` be a relative group law on a separated `f : A ⟶ Spec K`, and
let `ev` be a family of additive identifications, one for every field `F` over `K`, of the
points of `A` over `F` with the `F`-points of a Weierstrass curve `W`. If `W` has no nonzero
`q`-torsion `K`-point, then any Drinfeld basis of `G` at level `q ≥ 2` consists of the unit
sections. -/
theorem IsDrinfeldBasis.eq_one_of_forall_nsmul_eq_zero [IsSeparated f]
    (hev : IsAdditivePointsEval W G ev) {q : ℕ} (hq : 2 ≤ q)
    (hss : ∀ R : W.toAffine.Point, q • R = 0 → R = 0) {P Q : Section f}
    (hPQ : IsDrinfeldBasis G q P Q) :
    P = G.one (𝟙 _) ∧ Q = G.one (𝟙 _) :=
  ⟨eq_one_of_isTorsionPoint hev hss (hPQ.isTorsionPoint hq).1,
    eq_one_of_isTorsionPoint hev hss (hPQ.isTorsionPoint hq).2⟩

end Field

end DrinfeldGlobal

end AlgebraicGeometry
