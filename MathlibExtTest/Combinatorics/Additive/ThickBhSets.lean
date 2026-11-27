/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ThickBhSets
import Mathlib.Data.List.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Tests for Bose's and Singer's constructions of `B_h`-sets -/

namespace MathlibExtTest.Combinatorics.Additive.ThickBhSets

open MetaMathlibExt
open scoped IntermediateField

/-- The construction over the two-element field gives three points in `ZMod 7`. -/
public theorem singerSet_two_card {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hK : Module.finrank (ZMod 2) K = 3) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly (ZMod 2) (θ ^ b)).natDegree = 3) :
    (singerSet (ZMod 2) 2 θ b).ncard = 3 := by
  simpa using (isBhSet_singerSet (F := ZMod 2) (h := 2) (by decide) hK hθ hb).2

/-- Equal two-term sums determine the same summands, allowing repetitions. -/
public theorem singerSet_two_perm {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hK : Module.finrank (ZMod 2) K = 3) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly (ZMod 2) (θ ^ b)).natDegree = 3)
    {a₁ a₂ c₁ c₂ : ZMod 7}
    (ha₁ : a₁ ∈ singerSet (ZMod 2) 2 θ b) (ha₂ : a₂ ∈ singerSet (ZMod 2) 2 θ b)
    (hc₁ : c₁ ∈ singerSet (ZMod 2) 2 θ b) (hc₂ : c₂ ∈ singerSet (ZMod 2) 2 θ b)
    (he : a₁ + a₂ = c₁ + c₂) : [a₁, a₂].Perm [c₁, c₂] := by
  have hBh := (isBhSet_singerSet (F := ZMod 2) (h := 2) (by decide) hK hθ hb).1
  apply hBh.2.2 [a₁, a₂] [c₁, c₂]
    (by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · exact hx ▸ ha₁
      · exact (List.mem_singleton.mp hx) ▸ ha₂)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · exact hx ▸ hc₁
      · exact (List.mem_singleton.mp hx) ▸ hc₂)
    rfl rfl (by simp) (by simp)
  change a₁ + a₂ = c₁ + c₂
  exact he

private abbrev F := ZMod 2
private abbrev K := GaloisField 2 2

private theorem degree_of_order_three {x : K} (hx : orderOf x = 3) :
    (minpoly F x).natDegree = 2 := by
  have hdvd := Module.finrank_dvd_finrank_right F F⟮x⟯ K
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x),
    GaloisField.finrank 2 (by decide)] at hdvd
  refine (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd).resolve_left ?_
  intro h
  obtain ⟨a, rfl⟩ := minpoly.natDegree_eq_one_iff.mp h
  rcases (show ∀ a : F, a = 0 ∨ a = 1 by decide) a with rfl | rfl <;> simp at hx

-- Membership pins the definition of the Bose set.
example (θ : K) (b : ℕ) (a : ZMod (Fintype.card F ^ 2 - 1)) :
    a ∈ boseSet F 2 θ b ↔ ∃ v : F, θ ^ a.val = θ ^ b + algebraMap F K v :=
  Iff.rfl

-- The quadratic extension of `ZMod 2` gives a `B_2`-set with `2` elements.
example : ∃ θ : K, orderOf θ = 3 ∧
    AdditiveCombinatorics.IsBhSet (boseSet F 2 θ 1) 2 ∧
      (boseSet F 2 θ 1).ncard = 2 := by
  classical
  let _ : Fintype K := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hc : Nat.card K = 4 := GaloisField.card 2 2 (by decide)
  have hθ : orderOf (g : K) = 3 := by rw [orderOf_units, hg, Nat.card_units, hc]
  have hb : (minpoly F ((g : K) ^ 1)).natDegree = 2 := by
    rw [pow_one]
    exact degree_of_order_three hθ
  have hcard : orderOf (g : K) = Fintype.card K - 1 := by
    rwa [Fintype.card_eq_nat_card, hc]
  have hmain := isBhSet_boseSet (by decide) (GaloisField.finrank 2 (by decide))
    hcard hb
  have hF : Fintype.card F = 2 := ZMod.card 2
  exact ⟨g, hθ, hmain.1, hmain.2.trans hF⟩

end MathlibExtTest.Combinatorics.Additive.ThickBhSets
