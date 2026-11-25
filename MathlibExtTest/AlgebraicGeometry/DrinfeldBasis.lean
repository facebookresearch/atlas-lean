/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.DrinfeldBasis

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace DrinfeldBasisTest

/-- Consumer with the original binders. -/
theorem exactSource {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (G : RelativeGroupLaw R f) (n : ℕ)
    (h : Flat (pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).left)) :
    Flat ((DrinfeldGlobal.torsionIdeal G n).subschemeι ≫
      pullback.snd f (𝟙 (Spec (CommRingCat.of R)))) :=
  DrinfeldGlobal.flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr G n h

/-- The same consumer in a higher universe. -/
theorem exactSource_univ1 {R : Type 1} [CommRing R] {A : Scheme.{1}}
    {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (G : RelativeGroupLaw R f) (n : ℕ)
    (h : Flat (pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).left)) :
    Flat ((DrinfeldGlobal.torsionIdeal G n).subschemeι ≫
      pullback.snd f (𝟙 (Spec (CommRingCat.of R)))) :=
  DrinfeldGlobal.flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr G n h

/-- For a commutative law the hypothesis is flatness of `schemeKerStr`, the
kernel of multiplication by `n`. -/
theorem exactSource_commutative {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (G : RelativeGroupLaw R f)
    (hc : G.IsCommutative) (n : ℕ) (h : Flat (G.schemeKerStr hc n)) :
    Flat ((DrinfeldGlobal.torsionIdeal G n).subschemeι ≫
      pullback.snd f (𝟙 (Spec (CommRingCat.of R)))) :=
  DrinfeldGlobal.flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr G n h

section Boundaries

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f) (P Q : DrinfeldGlobal.Section f)

/-- At level zero the basis tuple is empty, so the basis divisor is the
unit ideal. -/
theorem basisDivisor_zero : DrinfeldGlobal.basisDivisor G 0 P Q = ⊤ :=
  prodKerGraph_zero f _ _

/-- At level zero the source predicate `IsDrinfeldBasis` ignores the sections:
it says that the torsion ideal is the unit ideal. -/
theorem isDrinfeldBasis_zero_iff :
    DrinfeldGlobal.IsDrinfeldBasis G 0 P Q ↔ DrinfeldGlobal.torsionIdeal G 0 = ⊤ := by
  rw [DrinfeldGlobal.isDrinfeldBasis_iff, basisDivisor_zero, eq_comm]

/-- Level zero is not a level of `IsValidDrinfeldBasis`, whatever the sections. -/
theorem not_isValidDrinfeldBasis_zero : ¬ DrinfeldGlobal.IsValidDrinfeldBasis G 0 P Q :=
  fun h => Nat.lt_irrefl 0 h.level_pos

/-- At level one the only index is `(0, 0)`, so the basis tuple is the unit
section and ignores both `P` and `Q`. -/
theorem basisTuple_one (i : Fin (1 * 1)) :
    DrinfeldGlobal.basisTuple G 1 P Q i = (G.one (𝟙 (Spec (CommRingCat.of R)))).left := by
  simp [DrinfeldGlobal.basisTuple, DrinfeldGlobal.linComb, G.one_mul]

/-- At level one the source predicate `IsDrinfeldBasis` holds for every pair
of sections: the basis divisor and the torsion ideal are both the ideal of the
unit section. -/
theorem isDrinfeldBasis_one : DrinfeldGlobal.IsDrinfeldBasis G 1 P Q := by
  rw [DrinfeldGlobal.isDrinfeldBasis_iff]
  set e := (G.one (𝟙 (Spec (CommRingCat.of R)))).left
  have hgraph : ∀ (x : Spec (CommRingCat.of R) ⟶ A) (hx : x ≫ f = 𝟙 _), x = e →
      (graphOver f x hx).ker = (e ≫ DrinfeldGlobal.toPullbackId (f := f)).ker := by
    rintro x hx rfl
    congr 1
    apply pullback.hom_ext <;> simp [DrinfeldGlobal.toPullbackId, hx]
  have h1 : G.schemeNsmul 1 = 𝟙 A := by
    rw [RelativeGroupLaw.schemeNsmul, RelativeGroupLaw.nsmul_one]
    rfl
  have hfst : pullback.fst (G.schemeNsmul 1) e = pullback.snd (G.schemeNsmul 1) e ≫ e := by
    rw [← pullback.condition, h1, Category.comp_id]
  have : IsIso (G.schemeNsmul 1) := by rw [h1]; infer_instance
  rw [DrinfeldGlobal.basisDivisor, prodKerGraph_one,
    hgraph _ _ (basisTuple_one G P Q 0), DrinfeldGlobal.torsionIdeal, hfst, Category.assoc,
    Scheme.Hom.ker_comp_of_isIso (pullback.snd _ _)]

/-- At level one `IsValidDrinfeldBasis` holds exactly for the unit pair: its
torsion conditions rule out every other pair. -/
theorem isValidDrinfeldBasis_one_iff :
    DrinfeldGlobal.IsValidDrinfeldBasis G 1 P Q ↔
      P = G.one (𝟙 (Spec (CommRingCat.of R))) ∧ Q = G.one (𝟙 (Spec (CommRingCat.of R))) := by
  constructor
  · intro h
    have hP := (G.isTorsionPoint_def _ _ _).mp h.isTorsionPoint_fst
    have hQ := (G.isTorsionPoint_def _ _ _).mp h.isTorsionPoint_snd
    rw [RelativeGroupLaw.nsmul_one] at hP hQ
    exact ⟨hP, hQ⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨Nat.one_pos, G.nsmul_one_point _ 1, G.nsmul_one_point _ 1, isDrinfeldBasis_one G _ _⟩

/-- At level two the combination of `a` copies of `P` and `b` copies of `Q`
sits at index `2 * a + b`, so index `1` is `Q`. -/
theorem basisTuple_two_one : DrinfeldGlobal.basisTuple G 2 P Q ⟨1, by decide⟩ = Q.left := by
  simp [DrinfeldGlobal.basisTuple, DrinfeldGlobal.linComb, G.one_mul]

/-- At level two index `2` is `P`. -/
theorem basisTuple_two_two : DrinfeldGlobal.basisTuple G 2 P Q ⟨2, by decide⟩ = P.left := by
  simp [DrinfeldGlobal.basisTuple, DrinfeldGlobal.linComb, G.one_mul, G.mul_one]

end Boundaries

end DrinfeldBasisTest
