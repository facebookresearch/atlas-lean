/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MilnorComparison
public import MathlibExt.KTheory.Ring.K2.K2SteinbergSpanning
public import MathlibExt.KTheory.Ring.K2.MatsumotoReverseSymbol

/-! # Inverses for Matsumoto

Milnor-side composite: the composite

  `matsumotoReverse ∘ milnorComparison`

is unconditionally the identity on `MilnorK F 2`, by applying the retained
conditional theorem `matsumotoReverse_comp_milnorComparison_eq_id` to the
accepted symbol bridge
`MatsumotoStableExtensionDiagram.matsumotoReverse_steinbergSymbol`.

K2-side composite: if in addition
`ker toStableE = torusCocycleSubgroup` holds, then
`K2_closure_steinbergSymbolProd_eq_top` gives Steinberg-symbol spanning of
`K2`, and combined with the same symbol bridge the composite

  `milnorComparison ∘ matsumotoReverse`

is the identity on `Additive (K2 F)`. This direction is conditional on both
the symbol bridge and `ker toStableE = torusCocycleSubgroup` through
Steinberg-symbol spanning.

No unconditional K₂-side identity, full kernel equality, unconditional
`matsumotoAddEquiv`, Matsumoto isomorphism, or naturality is established in
this file: the K₂-side composite and `matsumotoAddEquiv` remain conditional on
the hypotheses stated above, and kernel equality and naturality are absent.
-/

@[expose] public section

open scoped IsMulCommutative

universe u

namespace AlgebraicKTheory.K2

variable (F : Type u) [Field F]

/-- Conditional Milnor-side inverse: if `matsumotoReverse` agrees with
`MilnorK.k2Symbol` on every algebraic Steinberg symbol, then its composite
with `milnorComparison` is the identity on `MilnorK F 2` as a `ℤ`-linear map.

This is stated as equality of `ℤ`-linear maps via `toIntLinearMap`,
so `k2Symbol_ext` applies directly and the bridge theorem can discharge `h`. -/
theorem matsumotoReverse_comp_milnorComparison_eq_id
    (h : ∀ (a b : Fˣ), matsumotoReverse F (Additive.ofMul (steinbergSymbol a b)) =
        MilnorK.k2Symbol F a b) :
    (matsumotoReverse F).toIntLinearMap.comp (milnorComparison F) = LinearMap.id := by
  apply MilnorK.k2Symbol_ext (F := F)
  intro a b
  simp only [LinearMap.comp_apply, LinearMap.id_apply, milnorComparison_k2Symbol,
    AddMonoidHom.coe_toIntLinearMap]
  exact h a b

/-- Unconditional Milnor-side inverse: the composite
`matsumotoReverse ∘ milnorComparison` is the identity on `MilnorK F 2` as a
`ℤ`-linear map.

This applies the retained conditional theorem
`matsumotoReverse_comp_milnorComparison_eq_id` to the accepted symbol bridge
`MatsumotoStableExtensionDiagram.matsumotoReverse_steinbergSymbol`. The K₂-side
identity, full kernel equality, `matsumotoAddEquiv`, and naturality remain
conditional or absent as documented in this module. -/
theorem matsumotoReverse_comp_milnorComparison_eq_id_unconditional :
    (matsumotoReverse F).toIntLinearMap.comp (milnorComparison F) = LinearMap.id :=
  matsumotoReverse_comp_milnorComparison_eq_id (F := F)
    (MatsumotoStableExtensionDiagram.matsumotoReverse_steinbergSymbol (F := F))

/-- Conditional K₂-side inverse: if `ker toStableE = torusCocycleSubgroup` and
`matsumotoReverse` sends every algebraic Steinberg symbol to the Milnor symbol,
then `milnorComparison ∘ matsumotoReverse` is the identity on `Additive (K2 F)`.

Uses `K2_closure_steinbergSymbolProd_eq_top` for spanning and
`milnorComparison_k2Symbol` for the symbol-level computation. No stronger
generator theorem is assumed. -/
theorem milnorComparison_comp_matsumotoReverse_eq_id
    (hKer : MonoidHom.ker (StableSteinberg.toStableE (R := F)) =
      StableSteinberg.torusCocycleSubgroup (F := F))
    (h : ∀ (a b : Fˣ), matsumotoReverse F (Additive.ofMul (steinbergSymbol a b)) =
        MilnorK.k2Symbol F a b) :
    (milnorComparison F).toAddMonoidHom.comp (matsumotoReverse F) =
      AddMonoidHom.id (Additive (K2 F)) := by
  let g : Additive (K2 F) →+ Additive (K2 F) :=
    (milnorComparison F).toAddMonoidHom.comp (matsumotoReverse F)
  have hg_fix_steinberg : ∀ (a b : Fˣ),
      g (Additive.ofMul (steinbergSymbol a b)) = Additive.ofMul (steinbergSymbol a b) := by
    intro a b
    simp only [g, AddMonoidHom.comp_apply, h a b]
    exact milnorComparison_k2Symbol F a b
  let S : Subgroup (K2 F) :=
    { carrier := { x | g (Additive.ofMul x) = Additive.ofMul x }
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred] at *
        calc g (Additive.ofMul (a * b))
            = g (Additive.ofMul a + Additive.ofMul b) := rfl
          _ = g (Additive.ofMul a) + g (Additive.ofMul b) := by
              exact AddMonoidHom.map_add g (Additive.ofMul a) (Additive.ofMul b)
          _ = Additive.ofMul a + Additive.ofMul b := by rw [ha, hb]
          _ = Additive.ofMul (a * b) := rfl
      one_mem' := by
        simp only [Set.mem_ofPred]
        have h_one : Additive.ofMul (1 : K2 F) = (0 : Additive (K2 F)) := rfl
        calc g (Additive.ofMul (1 : K2 F))
            = g (0 : Additive (K2 F)) := by rw [h_one]
          _ = 0 := by exact AddMonoidHom.map_zero g
          _ = Additive.ofMul (1 : K2 F) := by rw [h_one]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred] at *
        have h_inv : Additive.ofMul (a⁻¹) = -Additive.ofMul a := by
          exact ofMul_inv a
        calc g (Additive.ofMul (a⁻¹))
            = g (-Additive.ofMul a) := by rw [h_inv]
          _ = -g (Additive.ofMul a) := by exact AddMonoidHom.map_neg g (Additive.ofMul a)
          _ = -Additive.ofMul a := by rw [ha]
          _ = Additive.ofMul (a⁻¹) := by rw [← h_inv] }
  have h_range_le : Set.range (steinbergSymbolProd (F := F)) ≤ (S : Set (K2 F)) := by
    intro y hy
    obtain ⟨⟨a, b⟩, rfl⟩ := hy
    simp only [steinbergSymbolProd]
    exact hg_fix_steinberg a b
  have h_closure_le :
      Subgroup.closure (Set.range (steinbergSymbolProd (F := F))) ≤ S := by
    rw [Subgroup.closure_le]
    exact h_range_le
  have h_top : Subgroup.closure (Set.range (steinbergSymbolProd (F := F))) = ⊤ :=
    K2_closure_steinbergSymbolProd_eq_top (F := F) hKer
  have h_all : ∀ (x : K2 F), g (Additive.ofMul x) = Additive.ofMul x := by
    intro x
    have hx_mem_closure :
        x ∈ Subgroup.closure (Set.range (steinbergSymbolProd (F := F))) := by
      rw [h_top]
      trivial
    have hx_mem_S : x ∈ S := h_closure_le hx_mem_closure
    exact hx_mem_S
  apply AddMonoidHom.ext
  intro y
  have hy_eq : y = Additive.ofMul (Additive.toMul y) := (ofMul_toMul y).symm
  have h1 : g y = g (Additive.ofMul (Additive.toMul y)) := congrArg g hy_eq
  have h2 : g (Additive.ofMul (Additive.toMul y)) = Additive.ofMul (Additive.toMul y) :=
    h_all (Additive.toMul y)
  have h3 : Additive.ofMul (Additive.toMul y) = y := ofMul_toMul y
  calc g y = y := Eq.trans h1 (Eq.trans h2 h3)
    _ = (AddMonoidHom.id (Additive (K2 F))) y := rfl

/-- Conditional Matsumoto additive equivalence `MilnorK F 2 ≃+ Additive (K2 F)`.

Forward map is the existing `milnorComparison F`; inverse is `matsumotoReverse F`.
This is conditional on the symbol bridge
`∀ a b, matsumotoReverse (steinbergSymbol a b) = k2Symbol a b` and on
`MonoidHom.ker (StableSteinberg.toStableE (R := F)) = torusCocycleSubgroup`.
No unconditional Matsumoto isomorphism is established in this file. -/
noncomputable def matsumotoAddEquiv
    (h : ∀ (a b : Fˣ), matsumotoReverse F (Additive.ofMul (steinbergSymbol a b)) =
        MilnorK.k2Symbol F a b)
    (hKer : MonoidHom.ker (StableSteinberg.toStableE (R := F)) =
      StableSteinberg.torusCocycleSubgroup (F := F)) :
    MilnorK F 2 ≃+ Additive (K2 F) where
  toFun := milnorComparison F
  invFun := matsumotoReverse F
  left_inv := by
    intro x
    have hComp := matsumotoReverse_comp_milnorComparison_eq_id (F := F) h
    have hx : ((matsumotoReverse F).toIntLinearMap.comp (milnorComparison F)) x = x := by
      rw [hComp]
      rfl
    simp only [LinearMap.comp_apply] at hx
    -- `toIntLinearMap` has the same underlying function as the `AddMonoidHom`
    rw [AddMonoidHom.coe_toIntLinearMap] at hx
    exact hx
  right_inv := by
    intro y
    have hComp := milnorComparison_comp_matsumotoReverse_eq_id (F := F) hKer h
    have hy : ((milnorComparison F).toAddMonoidHom.comp (matsumotoReverse F)) y = y := by
      rw [hComp]
      rfl
    simp only [AddMonoidHom.comp_apply] at hy
    -- `toAddMonoidHom` has the same underlying function as the linear map
    rw [LinearMap.toAddMonoidHom_coe] at hy
    exact hy
  map_add' := by
    intro x y
    exact (milnorComparison F).map_add x y

end AlgebraicKTheory.K2

end
