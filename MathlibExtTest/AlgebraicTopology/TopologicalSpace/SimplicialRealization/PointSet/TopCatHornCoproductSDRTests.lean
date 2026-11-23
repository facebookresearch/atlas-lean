/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.TopCatHornCoproductSDR

@[expose] public section

/-!
# Horn-coproduct SDR client

Public clients for the generic SDR pushout theorem and the dependent horn-
coproduct retraction, homotopy, fixed law, Arrow iso, and pushout theorem.
Supplies no premise, adds no instance, and claims no transfinite composition
or model structure.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductSDRTests

/-- Bundled retract law as given by the provider. -/
theorem hornSDR_retract_client (J : Type 0) (n : J → ℕ) (k : ∀ j, Fin (n j + 1))
    (hn : ∀ j, 0 < n j) :
    TopCat.ofHom (TopCat.hornSDRCopIncl J n k) ≫
      TopCat.ofHom (TopCat.hornSDRCopRetract J n k hn) = 𝟙 _ :=
  TopCat.hornSDR_retract' J n k hn

/-- Bundled homotopy as given by the provider. -/
noncomputable def hornSDR_homotopy_client (J : Type 0) (n : J → ℕ)
    (k : ∀ j, Fin (n j + 1)) (hn : ∀ j, 0 < n j) :
    TopCat.Homotopy (𝟙 (TopCat.of (Σ j : J, ↥(TopCat.hornSDRSimplex J n j))))
      (TopCat.ofHom (TopCat.hornSDRCopRetract J n k hn) ≫
        TopCat.ofHom (TopCat.hornSDRCopIncl J n k)) :=
  TopCat.hornSDRHomotopyTop' J n k hn

/-- Bundled homotopy fix as given by the provider. -/
theorem hornSDR_fix_client (J : Type 0) (n : J → ℕ) (k : ∀ j, Fin (n j + 1))
    (hn : ∀ j, 0 < n j) (t : unitInterval)
    (a : ↥(TopCat.of (Σ j : J, ↥(TopCat.hornSDRDomain J n k j)))) :
    (TopCat.hornSDRHomotopyTop' J n k hn)
        (t, TopCat.ofHom (TopCat.hornSDRCopIncl J n k) a) =
      TopCat.ofHom (TopCat.hornSDRCopIncl J n k) a :=
  TopCat.hornSDR_stat' J n k hn t a

/-- Pushout leg as given by the provider. -/
theorem hornSDR_pushout_client (J : Type 0) (n : J → ℕ) (k : ∀ j, Fin (n j + 1))
    (hn : ∀ j, 0 < n j) {Y P : TopCat.{0}}
    {f : TopCat.of (Σ j : J, ↥(TopCat.hornSDRDomain J n k j)) ⟶ Y}
    {g : TopCat.of (Σ j : J, ↥(TopCat.hornSDRSimplex J n j)) ⟶ P} {j : Y ⟶ P}
    (h : IsPushout (TopCat.ofHom (TopCat.hornSDRCopIncl J n k)) f g j) :
    TopCat.weakHomotopyEquivalences j :=
  TopCat.hornSDR_pushout_inr_mem J n k hn h

#print axioms TopCat.hornSDR_pushout_inr_mem
#print axioms hornSDR_pushout_client

theorem genericSDRPushout_symbolic
    {A X Y P : TopCat.{u}} {i : A ⟶ X} {f : A ⟶ Y}
    {g : X ⟶ P} {j : Y ⟶ P} (h : IsPushout i f g j)
    (r : X ⟶ A) (retract : i ≫ r = 𝟙 A)
    (H : TopCat.Homotopy (𝟙 X) (r ≫ i))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    TopCat.weakHomotopyEquivalences j :=
  TopCat.sdr_pushout_inr_mem_weakHomotopyEquivalences h r retract H stat

theorem hornSDR_retract_symbolic
    (J : Type u) (n : J → ℕ) (k : ∀ j, Fin (n j + 1))
    (hn : ∀ j, 0 < n j) :
    TopCat.ofHom (TopCat.hornSDRCopIncl J n k) ≫
      TopCat.ofHom (TopCat.hornSDRCopRetract J n k hn) = 𝟙 _ :=
  TopCat.hornSDR_retract' J n k hn

noncomputable def hornSDR_homotopy_symbolic
    (J : Type u) (n : J → ℕ) (k : ∀ j, Fin (n j + 1))
    (hn : ∀ j, 0 < n j) :
    TopCat.Homotopy
      (𝟙 (TopCat.of (Σ j : J, ↥(TopCat.hornSDRSimplex J n j))))
      (TopCat.ofHom (TopCat.hornSDRCopRetract J n k hn) ≫
        TopCat.ofHom (TopCat.hornSDRCopIncl J n k)) :=
  TopCat.hornSDRHomotopyTop' J n k hn

theorem hornSDR_fix_symbolic
    (J : Type u) (n : J → ℕ) (k : ∀ j, Fin (n j + 1))
    (hn : ∀ j, 0 < n j) (t : unitInterval)
    (a : ↥(TopCat.of (Σ j : J,
      ↥(TopCat.hornSDRDomain J n k j)))) :
    (TopCat.hornSDRHomotopyTop' J n k hn)
        (t, TopCat.ofHom (TopCat.hornSDRCopIncl J n k) a) =
      TopCat.ofHom (TopCat.hornSDRCopIncl J n k) a :=
  TopCat.hornSDR_stat' J n k hn t a

noncomputable def hornSDR_arrowIso_symbolic
    (J : Type u) (n : J → ℕ) (k : ∀ j, Fin (n j + 1)) :
    Arrow.mk (Limits.Sigma.map
      (fun j : J => TopCat.hornSDRIncl J n k j)) ≅
      Arrow.mk (TopCat.ofHom (TopCat.hornSDRCopIncl J n k)) :=
  TopCat.hornSDR_arrow_iso J n k

theorem hornSDR_pushout_symbolic
    (J : Type u) (n : J → ℕ) (k : ∀ j, Fin (n j + 1))
    (hn : ∀ j, 0 < n j) {Y P : TopCat.{u}}
    {f : TopCat.of (Σ j : J,
      ↥(TopCat.hornSDRDomain J n k j)) ⟶ Y}
    {g : TopCat.of (Σ j : J,
      ↥(TopCat.hornSDRSimplex J n j)) ⟶ P}
    {j : Y ⟶ P}
    (h : IsPushout
      (TopCat.ofHom (TopCat.hornSDRCopIncl J n k)) f g j) :
    TopCat.weakHomotopyEquivalences j :=
  TopCat.hornSDR_pushout_inr_mem J n k hn h

theorem hornSDR_retract_u1
    (J : Type 1) (n : J → ℕ) (k : ∀ j, Fin (n j + 1))
    (hn : ∀ j, 0 < n j) :
    TopCat.ofHom (TopCat.hornSDRCopIncl J n k) ≫
      TopCat.ofHom (TopCat.hornSDRCopRetract J n k hn) = 𝟙 _ :=
  TopCat.hornSDR_retract' J n k hn

#print axioms TopCat.sdr_pushout_inr_mem_weakHomotopyEquivalences

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductSDRTests
