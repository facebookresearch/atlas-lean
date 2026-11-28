/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.TowerQuotientDatum

@[expose] public section

open CategoryTheory AlgebraicGeometry

/-- `exactSource` consumer with the original binders. -/
example
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0})
    (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (T : Scheme.{0}) (w : ∀ n : ℕ, X n ⟶ T)
    (hinv : ∀ (n : ℕ) (g : G), (a n g).asIso.hom ≫ w n = w n)
    (hxt : ∀ n : ℕ, xt n ≫ w (n + 1) = w n) :
    ∃! u : ∀ n : ℕ, D.Y n ⟶ T, ∀ n : ℕ, D.p n ≫ u n = w n :=
  TowerQuotientDatum.existsUnique_forall_p_comp_eq 𝒪 π X xb xt G a D T w hinv hxt

/-- The descended family exists: the existence half of the descent statement,
extracted without assuming anything beyond the datum and the two
compatibility hypotheses. -/
example
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0})
    (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (T : Scheme.{0}) (w : ∀ n : ℕ, X n ⟶ T)
    (hinv : ∀ (n : ℕ) (g : G), (a n g).asIso.hom ≫ w n = w n)
    (hxt : ∀ n : ℕ, xt n ≫ w (n + 1) = w n) :
    ∃ u : ∀ n : ℕ, D.Y n ⟶ T, ∀ n : ℕ, D.p n ≫ u n = w n :=
  (TowerQuotientDatum.existsUnique_forall_p_comp_eq 𝒪 π X xb xt G a D T w hinv hxt).exists
