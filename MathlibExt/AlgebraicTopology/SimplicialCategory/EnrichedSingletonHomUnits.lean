/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomUnitsAndEmpty

/-!
# Whole composition at an original singleton enriched Hom

When the actual source identity is a Hom isomorphism from the scalar
tensor unit, an identity-preserving diagonal map composes correctly with
any supplied whole Hom map. This includes an independently constructed
outer Horn map; no transported-functor outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.SingletonHomUnits

private theorem unit_elem {Y : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ Y) [IsIso e]
    (q : SimplexCategoryᵒᵖ) (p : Y.obj q) : p = (e.app q) PUnit.unit := by
  have h := congrArg (fun m : Y ⟶ Y => (m.app q) p) (IsIso.inv_hom_id e)
  change (e.app q) ((inv e).app q p) = p at h
  have h₀ : (inv e).app q p = PUnit.unit := @Subsingleton.elim PUnit.{u + 1} inferInstance _ _
  rw [h₀] at h
  exact h.symm

/-- A whole diagonal map preserving the original identity composes with every supplied Hom
map when the
  source diagonal Hom is genuinely the tensor unit. -/
theorem left_comp {A B : Carrier.{u}} (a b : A) (x y : B)
    [IsIso (eId SSet.{u} a)]
    (d : (a ⟶[SSet.{u}] a) ⟶ (x ⟶[SSet.{u}] x)) (m : (a ⟶[SSet.{u}] b) ⟶ (x ⟶[SSet.{u}] y))
    (hd : eId SSet.{u} a ≫ d = eId SSet.{u} x) :
    eComp SSet.{u} a a b ≫ m = (d ⊗ₘ m) ≫ eComp SSet.{u} x x y := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  rintro ⟨p₀, p₁⟩
  have h₀ := unit_elem (eId SSet.{u} a) q p₀
  have hS := congrArg (fun h : (a ⟶[SSet.{u}] b) ⟶ (a ⟶[SSet.{u}] b) =>
    (h.app q) p₁) (e_id_comp SSet.{u} a b)
  change (eComp SSet.{u} a a b).app q ((eId SSet.{u} a).app q PUnit.unit, p₁) = p₁ at hS
  have hD := congrArg (fun h : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] x) => (h.app q) PUnit.unit) hd
  change (d.app q) ((eId SSet.{u} a).app q PUnit.unit) = (eId SSet.{u} x).app q PUnit.unit at hD
  have hT := congrArg (fun h : (x ⟶[SSet.{u}] y) ⟶ (x ⟶[SSet.{u}] y) =>
    (h.app q) ((m.app q) p₁)) (e_id_comp
    SSet.{u} x y)
  change (eComp SSet.{u} x x y).app q ((eId SSet.{u} x).app q PUnit.unit, (m.app q) p₁) =
    (m.app q) p₁ at hT
  change (m.app q) ((eComp SSet.{u} a a b).app q (p₀, p₁)) =
    (eComp SSet.{u} x x y).app q ((d.app q) p₀, (m.app q) p₁)
  rw [h₀, hS, hD]
  exact hT.symm

/-- The actual right diagonal identity composes with any supplied whole Hom map under the
same genuine
  singleton source-Hom hypothesis. -/
theorem right_comp {A B : Carrier.{u}} (a b : A) (x y : B)
    [IsIso (eId SSet.{u} b)]
    (d : (b ⟶[SSet.{u}] b) ⟶ (y ⟶[SSet.{u}] y)) (m : (a ⟶[SSet.{u}] b) ⟶ (x ⟶[SSet.{u}] y))
    (hd : eId SSet.{u} b ≫ d = eId SSet.{u} y) :
    eComp SSet.{u} a b b ≫ m = (m ⊗ₘ d) ≫ eComp SSet.{u} x y y := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  rintro ⟨p₀, p₁⟩
  have h₁ := unit_elem (eId SSet.{u} b) q p₁
  have hS := congrArg (fun h : (a ⟶[SSet.{u}] b) ⟶ (a ⟶[SSet.{u}] b) =>
    (h.app q) p₀) (e_comp_id SSet.{u} a b)
  change (eComp SSet.{u} a b b).app q (p₀, (eId SSet.{u} b).app q PUnit.unit) = p₀ at hS
  have hD := congrArg (fun h : 𝟙_ SSet.{u} ⟶ (y ⟶[SSet.{u}] y) => (h.app q) PUnit.unit) hd
  change (d.app q) ((eId SSet.{u} b).app q PUnit.unit) = (eId SSet.{u} y).app q PUnit.unit at hD
  have hT := congrArg (fun h : (x ⟶[SSet.{u}] y) ⟶ (x ⟶[SSet.{u}] y) =>
    (h.app q) ((m.app q) p₀)) (e_comp_id
    SSet.{u} x y)
  change (eComp SSet.{u} x y y).app q ((m.app q) p₀, (eId SSet.{u} y).app q PUnit.unit) =
    (m.app q) p₀ at hT
  change (m.app q) ((eComp SSet.{u} a b b).app q (p₀, p₁)) =
    (eComp SSet.{u} x y y).app q ((m.app q) p₀, (d.app q) p₁)
  rw [h₁, hS, hD]
  exact hT.symm

end CategoryTheory.SimplicialEnrichment.SingletonHomUnits
