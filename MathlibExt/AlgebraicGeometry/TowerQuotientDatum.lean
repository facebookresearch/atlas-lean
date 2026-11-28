/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq.lean`,
`Definitions/Def_AlgebraicGeometry_TowerQuotientDatum.lean`
and
`P2M/Sol/S_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq.lean`
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

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

/-- A quotient datum for a tower of schemes over the quotients of a ring
by powers of an element `π`.

The tower `X n` carries a group action and maps to a tower `Y n`; the maps
`p n : X n ⟶ Y n` are finite and surjective, are invariant under the group
action, satisfy a local universal property (`univ_loc`), and have the
expected fibres over algebraically closed fields and over adic valuation
rings. -/
structure TowerQuotientDatum
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0})
    (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] (a : ∀ n : ℕ, G →* Aut (X n)) : Type 1 where
  /-- The quotient tower. -/
  Y : ℕ → Scheme.{0}
  /-- The structure maps of the quotient tower. -/
  yb : ∀ n : ℕ, Y n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))
  /-- The transition maps of the quotient tower. -/
  yt : ∀ n : ℕ, Y n ⟶ Y (n + 1)
  /-- The transition squares of the quotient tower are pullbacks. -/
  yt_isPullback : ∀ n : ℕ, IsPullback (yt n) (yb n) (yb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow π (Nat.le_succ (n + 1)))))))
  /-- The structure maps of the quotient tower are proper. -/
  yb_isProper : ∀ n : ℕ, IsProper (yb n)
  /-- The structure maps of the quotient tower are flat. -/
  yb_flat : ∀ n : ℕ, Flat (yb n)
  /-- The quotient maps. -/
  p : ∀ n : ℕ, X n ⟶ Y n
  /-- The quotient maps commute with the structure maps. -/
  p_over : ∀ n : ℕ, p n ≫ yb n = xb n
  /-- The quotient maps commute with the transition maps. -/
  p_xt : ∀ n : ℕ, xt n ≫ p (n + 1) = p n ≫ yt n
  /-- The transition squares for the quotient maps are pullbacks. -/
  p_isPullback : ∀ n : ℕ, IsPullback (xt n) (p n) (p (n + 1)) (yt n)
  /-- The quotient maps are invariant under the group action. -/
  p_inv : ∀ (n : ℕ) (g : G), (a n g).asIso.hom ≫ p n = p n
  /-- The quotient maps are finite. -/
  p_isFinite : ∀ n : ℕ, IsFinite (p n)
  /-- The quotient maps are surjective. -/
  p_surjective : ∀ n : ℕ, Surjective (p n)
  /-- The quotient maps are epimorphisms locally on the target. -/
  p_epi_loc : ∀ (n : ℕ) (U : (Y n).Opens), Epi ((p n) ∣_ U)
  /-- The local universal property of the quotient maps. -/
  univ_loc : ∀ (T : Scheme.{0}) (U : ∀ n : ℕ, (Y n).Opens)
      (hU : ∀ n : ℕ, (yt n) ⁻¹ᵁ (U (n + 1)) = U n)
      (u : ∀ n : ℕ, (↑((p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T),
      (∀ (n : ℕ) (g : G),
        Scheme.Hom.resLE (a n g).asIso.hom ((p n) ⁻¹ᵁ (U n)) ((p n) ⁻¹ᵁ (U n))
          (by rw [← Scheme.Hom.comp_preimage, p_inv]) ≫ u n = u n) →
      (∀ n : ℕ,
        Scheme.Hom.resLE (xt n) ((p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((p n) ⁻¹ᵁ (U n))
          (by
            rw [← Scheme.Hom.comp_preimage, p_xt, Scheme.Hom.comp_preimage, hU]) ≫
          u (n + 1) = u n) →
      ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (p n) ∣_ (U n) ≫ v n = u n
  /-- Fibres over algebraically closed fields are single group orbits. -/
  fib : ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k]
      (y : Spec (CommRingCat.of k) ⟶ Y n),
      (∃ x : Spec (CommRingCat.of k) ⟶ X n, x ≫ p n = y) ∧
      ∀ x x' : Spec (CommRingCat.of k) ⟶ X n, x ≫ p n = y →
        (x' ≫ p n = y ↔ ∃ g : G, x' = x ≫ (a n g).asIso.hom)
  /-- Fibres over adic valuation rings are single group orbits. -/
  adicFib : ∀ (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra 𝒪 R],
      IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R → IsAlgClosed (FractionRing R) →
      ∀ (y : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span
          {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ Y n),
      (∀ n : ℕ, y n ≫ yb n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap
        (Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)}) (algebraMap 𝒪 R)
        (by
          rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
            Ideal.mem_comap, map_pow]
          exact Ideal.subset_span rfl)))) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr
            (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ y (n + 1) =
        y n ≫ yt n) →
      (∃ x : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span
            {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ X n,
        (∀ n : ℕ, x n ≫ p n = y n) ∧
        ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
            (Ideal.span_singleton_le_span_singleton.mpr
              (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x (n + 1) =
          x n ≫ xt n) ∧
      ∀ x x' : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span
            {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ X n,
        (∀ n : ℕ, x n ≫ p n = y n) → (∀ n : ℕ, x' n ≫ p n = y n) →
        (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
            (Ideal.span_singleton_le_span_singleton.mpr
              (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x (n + 1) =
          x n ≫ xt n) →
        (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
            (Ideal.span_singleton_le_span_singleton.mpr
              (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x' (n + 1) =
          x' n ≫ xt n) →
        ∃ g : G, ∀ n : ℕ, x' n = x n ≫ (a n g).asIso.hom

namespace TowerQuotientDatum

/-- A compatible family of invariant maps out of the tower `X` descends
uniquely to the quotient tower `Y`. -/
public theorem existsUnique_forall_p_comp_eq
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0})
    (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
    (D : AlgebraicGeometry.TowerQuotientDatum 𝒪 π X xb xt G a)
    (T : Scheme.{0}) (w : ∀ n : ℕ, X n ⟶ T)
    (hinv : ∀ (n : ℕ) (g : G), (a n g).asIso.hom ≫ w n = w n)
    (hxt : ∀ n : ℕ, xt n ≫ w (n + 1) = w n) :
    ∃! u : ∀ n : ℕ, D.Y n ⟶ T, ∀ n : ℕ, D.p n ≫ u n = w n := by
  have hepi : ∀ n : ℕ, Epi (D.p n) := by
    intro n
    haveI : Epi ((D.p n) ∣_ (⊤ : (D.Y n).Opens)) := D.p_epi_loc n ⊤
    haveI : IsIso (⊤ : (D.Y n).Opens).ι := by
      rw [← Scheme.topIso_hom]; infer_instance
    have h : Epi (((D.p n) ∣_ (⊤ : (D.Y n).Opens)) ≫ (⊤ : (D.Y n).Opens).ι) :=
      epi_comp _ _
    rw [morphismRestrict_ι] at h
    exact epi_of_epi ((D.p n) ⁻¹ᵁ (⊤ : (D.Y n).Opens)).ι (D.p n)
  obtain ⟨v, hv⟩ := D.univ_loc T (fun n => ⊤) (fun n => Scheme.Hom.preimage_top _)
    (fun n => ((D.p n) ⁻¹ᵁ (⊤ : (D.Y n).Opens)).ι ≫ w n)
    (fun n g => by rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hinv])
    (fun n => by rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hxt])
  have hex : ∀ n : ℕ, D.p n ≫ ((D.Y n).topIso.inv ≫ v n) = w n := by
    intro n
    haveI : IsIso ((D.p n) ⁻¹ᵁ (⊤ : (D.Y n).Opens)).ι := by
      rw [Scheme.Hom.preimage_top, ← Scheme.topIso_hom]; infer_instance
    rw [← cancel_epi ((D.p n) ⁻¹ᵁ (⊤ : (D.Y n).Opens)).ι, ← hv n, ← Category.assoc,
      ← morphismRestrict_ι, Category.assoc, ← Category.assoc (⊤ : (D.Y n).Opens).ι,
      Scheme.ι_toIso_inv, Category.id_comp]
  refine ⟨fun n => (D.Y n).topIso.inv ≫ v n, hex, fun u' hu' => funext fun n => ?_⟩
  exact (cancel_epi (D.p n)).mp ((hu' n).trans (hex n).symm)

end TowerQuotientDatum

end AlgebraicGeometry
