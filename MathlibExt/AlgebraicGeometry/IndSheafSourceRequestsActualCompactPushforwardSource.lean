/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Closure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

/-!
# Actual compact pushforward source for ind-sheaf proper direct image

Proves `WantedExt.AlgebraicGeometry.IndSheafSourceRequests.actual_compact_pushforward_source`:
for a continuous map into a Hausdorff space, ordinary sheaf pushforward sends
compactly supported sheaves to compactly supported sheaves. The support of the
pushforward is shown to lie in the continuous image of the support.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2/3.2/3.3;
Kashiwara--Schapira, Ind-sheaves.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IndSheafSourceRequests

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels

/-- Sections over an open vanish when all stalks above it vanish. -/
private theorem isZero_obj_of_forall_isZero_stalk (k : Type) [Field k] {X : TopCat.{0}}
    (F : OrdinarySheaf k X) (W : Opens X)
    (hW : ∀ x : X, x ∈ W → IsZero (F.presheaf.stalk x)) :
    IsZero (F.presheaf.obj (Opposite.op W)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun s ↦ ?_
  refine TopCat.Presheaf.section_ext F W s 0 fun x hx ↦ ?_
  have hsub := ModuleCat.subsingleton_of_isZero (hW x hx)
  exact hsub.elim _ _

open scoped _root_.AlgebraicGeometry in
/-- The stalk of a pushforward vanishes at points with a neighbourhood whose preimage
has vanishing stalks. -/
private theorem isZero_stalk_pushforward (k : Type) [Field k] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (F : OrdinarySheaf k X) (y : Y) (U₀ : Opens Y) (hy : y ∈ U₀)
    (h0 : ∀ x : X, x ∈ (Opens.map f).obj U₀ → IsZero (F.presheaf.stalk x)) :
    IsZero ((f _* F.presheaf).stalk y) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun t ↦ ?_
  obtain ⟨V, hyV, s, rfl⟩ := (f _* F.presheaf).exists_germ_eq t
  have hyW : y ∈ V ⊓ U₀ := ⟨hyV, hy⟩
  have hmaps := TopCat.Presheaf.germ_res_apply (f _* F.presheaf)
    (homOfLE inf_le_left : V ⊓ U₀ ⟶ V) y hyW s
  have hs0 : (f _* F.presheaf).map (homOfLE inf_le_left : V ⊓ U₀ ⟶ V).op s = 0 := by
    have hsub := ModuleCat.subsingleton_of_isZero
      (isZero_obj_of_forall_isZero_stalk k F ((Opens.map f).obj (V ⊓ U₀)) fun x hx ↦
        h0 x (by
          rw [Opens.mem_map] at hx ⊢
          exact (Opens.mem_inf.mp hx).2))
    exact hsub.elim _ _
  calc (f _* F.presheaf).germ V y hyV s
      = (f _* F.presheaf).germ (V ⊓ U₀) y hyW _ := hmaps.symm
    _ = 0 := by rw [hs0]; exact map_zero _

/-- Continuous image of actual compact support gives compact proper-image generators. -/
theorem actual_compact_pushforward_source (k : Type) [Field k]
    (X Y : TopCat.{0}) [T2Space Y] (f : X ⟶ Y) : CompactPushforwardSource k f := by
  refine ⟨fun F ↦ ?_⟩
  change IsCompact (ordinarySupport k Y ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).obj F.obj))
  have hS : IsCompact (ordinarySupport k X F.obj) := F.property
  have hK : IsCompact ((f.hom : X → Y) '' ordinarySupport k X F.obj) :=
    hS.image f.hom.continuous
  have hKclosed : IsClosed ((f.hom : X → Y) '' ordinarySupport k X F.obj) := hK.isClosed
  refine IsCompact.of_isClosed_subset hK isClosed_closure ?_
  refine closure_minimal ?_ hKclosed
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  by_contra hyK
  exact hy (isZero_stalk_pushforward k f F.obj y ⟨_, hKclosed.isOpen_compl⟩ hyK fun x hx ↦ by
    by_contra hx0
    have hxS : x ∈ ordinarySupport k X F.obj := subset_closure hx0
    have hmem : f.hom x ∈ (f.hom : X → Y) '' ordinarySupport k X F.obj := ⟨x, hxS, rfl⟩
    rw [Opens.mem_map] at hx
    exact hx hmem)

end WantedExt.AlgebraicGeometry.IndSheafSourceRequests
