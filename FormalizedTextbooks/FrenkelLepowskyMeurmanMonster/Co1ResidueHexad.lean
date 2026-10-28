/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueLocalGroup

/-! A direct group-theoretic proof of the overlapping-pair step in Ivanov II Lemma 3.4.4.
The six-element hexad geometry has pair points and perfect-matching lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A triple product relation and the last point involution determine the first pair product. -/
theorem co1ResidueHexad_pair_product {G : Type*} [Group G] (a b c : G)
    (hc : c * c = 1) (hline : a * b * c = 1) : a * b = c := by
  calc
    a * b = a * b * (c * c) := by rw [hc, mul_one]
    _ = (a * b * c) * c := by simp only [mul_assoc]
    _ = c := by rw [hline, one_mul]

/-- In a six-element hexad, the images of two overlapping pair points commute.
Every assumed triple is precisely a perfect matching of the six elements. -/
theorem co1ResidueHexad_overlapping_commute {G : Type*} [Group G]
    (x : Fin 6 → Fin 6 → G)
    (hsquare : ∀ a b, a ≠ b → x a b * x a b = 1)
    (hline : ∀ v : Fin 6 → Fin 6, Function.Bijective v →
      x (v 0) (v 1) * x (v 2) (v 3) * x (v 4) (v 5) = 1) :
    Commute (x 0 1) (x 0 2) := by
  have hp (v : Fin 6 → Fin 6) (hv : Function.Bijective v) :
      x (v 0) (v 1) * x (v 2) (v 3) = x (v 4) (v 5) :=
    co1ResidueHexad_pair_product _ _ _ (hsquare _ _ (hv.injective.ne (by decide +kernel)))
      (hline v hv)
  have h1 : x 2 3 * x 4 5 = x 0 1 := hp ![2, 3, 4, 5, 0, 1] (by decide +kernel)
  have h2 : x 4 5 * x 0 2 = x 1 3 := hp ![4, 5, 0, 2, 1, 3] (by decide +kernel)
  have h3 : x 1 5 * x 0 4 = x 2 3 := hp ![1, 5, 0, 4, 2, 3] (by decide +kernel)
  have h4 : x 0 4 * x 1 3 = x 2 5 := hp ![0, 4, 1, 3, 2, 5] (by decide +kernel)
  have h5 : x 2 5 * x 0 1 = x 3 4 := hp ![2, 5, 0, 1, 3, 4] (by decide +kernel)
  have h6 : x 1 5 * x 3 4 = x 0 2 := hp ![1, 5, 3, 4, 0, 2] (by decide +kernel)
  have ha := hsquare 0 1 (by decide +kernel)
  have hb := hsquare 0 2 (by decide +kernel)
  have hword : x 0 1 * x 0 2 * x 0 1 * x 0 2 = 1 := by
    calc
      x 0 1 * x 0 2 * x 0 1 * x 0 2 =
          x 2 3 * x 4 5 * x 0 2 * x 0 1 * x 0 2 := by rw [h1]
      _ = x 2 3 * x 1 3 * x 0 1 * x 0 2 := by rw [mul_assoc (x 2 3), h2]
      _ = x 1 5 * x 0 4 * x 1 3 * x 0 1 * x 0 2 := by rw [h3]
      _ = x 1 5 * x 2 5 * x 0 1 * x 0 2 := by rw [mul_assoc (x 1 5), h4]
      _ = x 1 5 * x 3 4 * x 0 2 := by rw [mul_assoc (x 1 5), h5]
      _ = x 0 2 * x 0 2 := by rw [h6]
      _ = 1 := hb
  have hconj : x 0 1 * x 0 2 * x 0 1 = x 0 2 := by
    have h := congrArg (fun y => y * x 0 2) hword
    simpa only [mul_assoc, hb, mul_one, one_mul] using h
  change x 0 1 * x 0 2 = x 0 2 * x 0 1
  calc
    x 0 1 * x 0 2 = x 0 1 * x 0 2 * (x 0 1 * x 0 1) := by rw [ha, mul_one]
    _ = (x 0 1 * x 0 2 * x 0 1) * x 0 1 := by simp only [mul_assoc]
    _ = x 0 2 * x 0 1 := by rw [hconj]

/-- Relabeling a hexad preserves the overlapping-pair commutation conclusion. -/
theorem co1ResidueHexad_overlapping_commute_relabel {G : Type*} [Group G]
    (x : Fin 6 → Fin 6 → G)
    (hsquare : ∀ a b, a ≠ b → x a b * x a b = 1)
    (hline : ∀ v : Fin 6 → Fin 6, Function.Bijective v →
      x (v 0) (v 1) * x (v 2) (v 3) * x (v 4) (v 5) = 1)
    (v : Fin 6 → Fin 6) (hv : Function.Bijective v) :
    Commute (x (v 0) (v 1)) (x (v 0) (v 2)) := by
  apply co1ResidueHexad_overlapping_commute (fun a b => x (v a) (v b))
  · intro a b hab
    exact hsquare _ _ (hv.injective.ne hab)
  · intro w hw
    exact hline (v ∘ w) (hv.comp hw)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
