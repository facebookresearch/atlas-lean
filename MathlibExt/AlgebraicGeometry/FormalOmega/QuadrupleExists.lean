/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`CF_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_forall_away`
`CF_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum
import MathlibExt.AlgebraicGeometry.FormalOmega.EdgeChart
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleUnique
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleBaseChange
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleGlue
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleLocal

/-!
# Existence of Drinfeld quadruples

Over an `𝒪`-algebra `B` in which `π` is nilpotent, every Deligne datum `d` admits a Drinfeld
datum `Q` that is a quadruple of `d` (`DeligneDatum.exists_drinfeldDatum_isQuadrupleOf`).

The proof covers `Spec B` by finitely many basic opens on which `d` lies in an edge chart whose
smaller lattice has determinant index `0`, constructs a quadruple on each of them, and glues
these local quadruples, which agree on overlaps up to unique isomorphism
(`DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_forall_away`).
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open LT.LatticeTree

namespace CerednikDrinfeld.FormalOmega.DeligneDatum

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
  [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} {B : Type} [CommRing B] [Algebra 𝒪 B]

/-- Quadruples of the base changes of a Deligne datum to the basic opens of a finite cover of
`Spec B` glue to a quadruple of the Deligne datum. -/
theorem exists_drinfeldDatum_isQuadrupleOf_of_forall_away (hπ : Irreducible π)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (d : DeligneDatum (K := K) π B)
    {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (hQ : ∀ i : Fin k, (Q i).IsQuadrupleOf
      (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))))) :
    ∃ Qg : DrinfeldDatum (K := K) π B, Qg.IsQuadrupleOf d := by
  classical
  let C : Fin k → Fin k → Type := fun i j =>
    Localization.Away (algebraMap B (Localization.Away (f i)) (f j))
  let algR : ∀ i j : Fin k, Algebra (Localization.Away (f j)) (C i j) := fun i j =>
    (IsLocalization.Away.awayToAwayLeft (f j) (f i) :
      Localization.Away (f j) →+*
        Localization.Away (algebraMap B (Localization.Away (f i)) (f j))).toAlgebra
  have towR : ∀ i j : Fin k, IsScalarTower B (Localization.Away (f j)) (C i j) := fun i j =>
    IsScalarTower.of_algebraMap_eq fun b =>
      (IsLocalization.Away.awayToAwayLeft_eq (f j) (f i) b).symm
  have towR𝒪 : ∀ i j : Fin k, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j) := fun i j =>
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f j)),
        ← IsScalarTower.algebraMap_apply B _ (C i j), IsScalarTower.algebraMap_apply 𝒪 B (C i j)]
  have locR : ∀ i j : Fin k,
      IsLocalization.Away (algebraMap B (Localization.Away (f j)) (f i)) (C i j) := fun i j =>
    IsLocalization.Away.commutes (Localization.Away (f j)) (Localization.Away (f i)) (C i j)
      (f j) (f i)
  have bc1 : ∀ i j : Fin k, ∃ Q₂ : DrinfeldDatum (K := K) π (C i j),
      (Q i).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) Q₂ :=
    fun i j => DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization (Q i)
      (Submonoid.powers (algebraMap B (Localization.Away (f i)) (f j))) (C i j)
  choose Q₂ hQ₂ using bc1
  have bc2 : ∀ i j : Fin k, ∃ Q₂' : DrinfeldDatum (K := K) π (C i j),
      (Q j).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) Q₂' :=
    fun i j => DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization (Q j)
      (Submonoid.powers (algebraMap B (Localization.Away (f j)) (f i))) (C i j)
  choose Q₂' hQ₂' using bc2
  have hmap : ∀ i j : Fin k,
      (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map π
          (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) =
        (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j)))).map π
          (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) := by
    intro i j
    have h1 := DeligneDatum.map_comp π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) d
    have h2 := DeligneDatum.map_comp π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j)))
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) d
    have h3 : (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)).comp
          (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) =
        (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)).comp
          (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) := by
      apply AlgHom.ext
      intro b
      simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
        ← IsScalarTower.algebraMap_apply]
    exact h1.symm.trans (h3 ▸ h2)
  have hd1 : ∀ i j : Fin k, (Q₂ i j).IsQuadrupleOf
      ((d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map π
        (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j))) := fun i j =>
    DrinfeldDatum.IsQuadrupleOf.map_of_isBaseChangeAlong _ (hQ i) (hQ₂ i j)
  have hd2 : ∀ i j : Fin k, (Q₂' i j).IsQuadrupleOf
      ((d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map π
        (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j))) := fun i j => by
    rw [hmap]
    exact DrinfeldDatum.IsQuadrupleOf.map_of_isBaseChangeAlong _ (hQ j) (hQ₂' i j)
  have hBC : ∀ i j : Fin k, IsNilpotent (algebraMap 𝒪 (C i j) π) := fun i j => by
    rw [IsScalarTower.algebraMap_apply 𝒪 B (C i j)]
    exact hB.map _
  have hiso : ∀ i j : Fin k, (Q₂' i j).IsIsomorphic (Q₂ i j) := fun i j =>
    (DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic hπ (hBC i j) (hd1 i j)
      (Q₂' i j)).mp (hd2 i j)
  have hr : ∀ i j : Fin k, (Q j).IsBaseChangeAlong
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j) := fun i j =>
    DrinfeldDatum.isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic _ (hQ₂' i j) (hiso i j)
  obtain ⟨Qg, hQg⟩ :=
    DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap f hf Q C Q₂ hQ₂ hr
  exact ⟨Qg, DrinfeldDatum.isQuadrupleOf_of_forall_isBaseChangeAlong_away f hf Qg d Q hQg hQ⟩

/-- Every Deligne datum over an `𝒪`-algebra in which `π` is nilpotent has a Drinfeld quadruple.
Here `𝒪` is a discrete valuation ring with uniformizer `π`, finite residue field and fraction
field `K`. -/
theorem exists_drinfeldDatum_isQuadrupleOf (hπ : Irreducible π)
    (hfin : Finite (𝒪 ⧸ Ideal.span {π})) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) : ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d := by
  classical
  obtain ⟨k, f, hf, M', M, hcov⟩ :=
    exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent hπ hfin hB d
  have hBi : ∀ i : Fin k, IsNilpotent (algebraMap 𝒪 (Localization.Away (f i)) π) := by
    intro i
    rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f i))]
    exact hB.map _
  have hQ : ∀ i : Fin k, ∃ Q : DrinfeldDatum (K := K) π (Localization.Away (f i)),
      Q.IsQuadrupleOf (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))) :=
    fun i => exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart hπ (hBi i) (hcov i).1
      (hcov i).2.1 (hcov i).2.2.1 _ (hcov i).2.2.2
  exact exists_drinfeldDatum_isQuadrupleOf_of_forall_away hπ hB d f hf
    (fun i => (hQ i).choose) (fun i => (hQ i).choose_spec)

end CerednikDrinfeld.FormalOmega.DeligneDatum

end
