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

public import MathlibExt.KTheory.Ring.K2.MatsumotoKernelGeneration

/-! # Steinberg-symbol spanning infrastructure

Product map, image equalities under `K₂.inclusion`, `range = ker`
via `ofKer`, and conditional `⊤` generation plus hom extensionality
assuming `ker toStableE = torusCocycleSubgroup`. No unconditional
kernel equality is asserted.
-/

@[expose] public section

universe u
namespace AlgebraicKTheory
namespace K2

variable {F : Type u} [Field F]

/-- Product-form Steinberg map `Fˣ × Fˣ → K₂ F`. -/
noncomputable def steinbergSymbolProd : Fˣ × Fˣ → K2 F :=
  fun p => steinbergSymbol p.1 p.2

/-- `inclusion` sends `steinbergSymbolProd` to `torusCocycleProd`. -/
theorem inclusion_steinbergSymbolProd (p : Fˣ × Fˣ) :
    K2.inclusion.app (RingCat.of F) (steinbergSymbolProd (F := F) p) =
      StableSteinberg.torusCocycleProd (F := F) p := by
  obtain ⟨u, v⟩ := p
  simpa only [steinbergSymbolProd, StableSteinberg.torusCocycleProd]
    using inclusion_steinbergSymbol (F := F) u v

/-- Image equality under `inclusion` vs `torusCocycleProd` range. -/
theorem inclusion_range_steinbergSymbolProd_eq_torusCocycleProd_range :
    Set.range (fun p : Fˣ × Fˣ =>
      K2.inclusion.app (RingCat.of F) (steinbergSymbolProd (F := F) p)) =
    Set.range (StableSteinberg.torusCocycleProd (F := F)) := by
  have h : (fun p : Fˣ × Fˣ => K2.inclusion.app (RingCat.of F)
      (steinbergSymbolProd (F := F) p)) = StableSteinberg.torusCocycleProd := by
    funext p; exact inclusion_steinbergSymbolProd (F := F) p
  exact congrArg Set.range h

/-- `torusCocycleProd` range equals image of `steinbergSymbolProd` under `inclusion`. -/
theorem torusCocycleProd_range_eq_image_steinberg :
    Set.range (StableSteinberg.torusCocycleProd (F := F)) =
    (K2.inclusion.app (RingCat.of F)).hom ''
      Set.range (steinbergSymbolProd (F := F)) := by
  ext y
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨steinbergSymbolProd p, ⟨p, rfl⟩, by rw [inclusion_steinbergSymbolProd]; exact hp⟩
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, (inclusion_steinbergSymbolProd p).symm⟩

/-- `MonoidHom.range inclusion = ker toStableE` via `ofKer` API. -/
theorem K2_inclusion_range_eq_ker_toStableE :
    MonoidHom.range (K2.inclusion.app (RingCat.of F)).hom =
    MonoidHom.ker (StableSteinberg.toStableE (R := F)) := by
  ext z
  constructor
  · rintro ⟨y, hy⟩; rw [← hy]; exact inclusion_apply_mem_ker y
  · intro hz; exact ⟨ofKer z (MonoidHom.mem_ker.mp hz), inclusion_ofKer z _⟩

/-- Conditional closure `⊤`: if `ker = torusCocycleSubgroup` then
Steinberg symbols generate `K₂`. Uses `Subgroup.map_closure` idea
and `comap_map` injectivity from `inclusion_injective`. -/
theorem K2_closure_steinbergSymbolProd_eq_top
    (hKer : MonoidHom.ker (StableSteinberg.toStableE (R := F)) =
      StableSteinberg.torusCocycleSubgroup (F := F)) :
    Subgroup.closure (Set.range (steinbergSymbolProd (F := F))) = ⊤ := by
  let f : K2 F →* StableSteinberg F := (K2.inclusion.app (RingCat.of F)).hom
  have hf_inj : Function.Injective f := inclusion_injective
  have h_range : MonoidHom.range f = MonoidHom.ker (StableSteinberg.toStableE (R := F)) :=
    K2_inclusion_range_eq_ker_toStableE (F := F)
  have h_torus : StableSteinberg.torusCocycleSubgroup (F := F) =
    Subgroup.closure (Set.range (StableSteinberg.torusCocycleProd (F := F))) := rfl
  have h_range_closure : MonoidHom.range f =
    Subgroup.closure (Set.range (StableSteinberg.torusCocycleProd (F := F))) := by
    rw [h_range, hKer, h_torus]
  have h_img : Set.range (StableSteinberg.torusCocycleProd (F := F)) =
    f '' Set.range (steinbergSymbolProd (F := F)) := by
    change Set.range (StableSteinberg.torusCocycleProd (F := F)) =
      (K2.inclusion.app (RingCat.of F)).hom '' Set.range (steinbergSymbolProd (F := F))
    exact torusCocycleProd_range_eq_image_steinberg (F := F)
  have h_closure_img : Subgroup.closure (Set.range (StableSteinberg.torusCocycleProd (F := F))) =
    Subgroup.closure (f '' Set.range (steinbergSymbolProd (F := F))) := by rw [h_img]
  have h_map_closure :
      Subgroup.map f (Subgroup.closure (Set.range (steinbergSymbolProd (F := F)))) =
        Subgroup.closure (f '' Set.range (steinbergSymbolProd (F := F))) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      exact fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩
    · rw [Subgroup.closure_le]
      intro y hy; obtain ⟨x, hx, rfl⟩ := hy
      exact Subgroup.mem_map.mpr ⟨x, Subgroup.subset_closure hx, rfl⟩
  have h_range_map_closure : MonoidHom.range f =
    Subgroup.map f (Subgroup.closure (Set.range (steinbergSymbolProd (F := F)))) := by
    rw [h_range_closure, h_closure_img, h_map_closure.symm]
  have h_map_top : Subgroup.map f (⊤ : Subgroup (K2 F)) = MonoidHom.range f := by
    ext y; simp [Subgroup.mem_map, MonoidHom.mem_range]
  have h_map_eq : Subgroup.map f (Subgroup.closure (Set.range (steinbergSymbolProd (F := F)))) =
    Subgroup.map f ⊤ := by rw [h_map_top, h_range_map_closure]
  have h_comap_map (S : Subgroup (K2 F)) : Subgroup.comap f (Subgroup.map f S) = S := by
    ext x; constructor
    · rintro ⟨y, hy, heq⟩; have : y = x := hf_inj heq; rwa [← this]
    · intro hx; exact ⟨x, hx, rfl⟩
  calc Subgroup.closure (Set.range (steinbergSymbolProd (F := F)))
      = Subgroup.comap f (Subgroup.map f (Subgroup.closure (Set.range (steinbergSymbolProd)))) := by
        rw [h_comap_map]
    _ = Subgroup.comap f (Subgroup.map f ⊤) := by rw [h_map_eq]
    _ = Subgroup.comap f (MonoidHom.range f) := by rw [← h_map_top]
    _ = ⊤ := by ext x; simp

/-- Extensionality: two `K₂ →* M` agreeing on Steinberg symbols are equal,
conditional on `ker = torusCocycleSubgroup`. -/
theorem K2_ext_of_steinbergSymbolProd {M : Type*} [Group M]
    (g₁ g₂ : K2 F →* M)
    (h_eq :
      ∀ p : Fˣ × Fˣ, g₁ (steinbergSymbolProd (F := F) p) = g₂ (steinbergSymbolProd (F := F) p))
    (hKer : MonoidHom.ker (StableSteinberg.toStableE (R := F)) =
      StableSteinberg.torusCocycleSubgroup (F := F)) :
    g₁ = g₂ := by
  have h_top : Subgroup.closure (Set.range (steinbergSymbolProd (F := F))) = ⊤ :=
    K2_closure_steinbergSymbolProd_eq_top (F := F) hKer
  let S : Subgroup (K2 F) :=
    { carrier := { x | g₁ x = g₂ x }
      mul_mem' := by
        intro a b ha hb; simp only [Set.mem_ofPred] at *; rw [map_mul, map_mul, ha, hb]
      one_mem' := by simp
      inv_mem' := by intro a ha; simp only [Set.mem_ofPred] at *; rw [map_inv, map_inv, ha] }
  have h_le : Set.range (steinbergSymbolProd (F := F)) ≤ S := by
    intro y hy; obtain ⟨p, rfl⟩ := hy; exact h_eq p
  have h_cl : Subgroup.closure (Set.range (steinbergSymbolProd (F := F))) ≤ S := by
    rwa [Subgroup.closure_le]
  rw [h_top] at h_cl; ext x; exact h_cl trivial

end K2
end AlgebraicKTheory
end
