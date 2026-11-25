/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Directed submodule unions as categorical colimits

The supremum submodule is the colimit of the directed system of inclusions.
Its universal linear map comes from the filtered-colimit universal property
on types and the stage inclusions. Scalar, carrier and index universes are
independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat.DirectedSubmoduleColimit

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {ι : Type w} [Preorder ι]

/-- The categorical directed-family diagram uses the actual submodule inclusions. -/
def diagram (S : ι → Submodule R M) (hS : Monotone S) : ι ⥤ ModuleCat.{v} R where
  obj i := ModuleCat.of R (S i)
  map f := ModuleCat.ofHom (Submodule.inclusion (hS (leOfHom f)))
  map_id i := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Every stage maps into the actual native supremum inside the original carrier. -/
def cocone (S : ι → Submodule R M) (hS : Monotone S) : Cocone (diagram S hS) where
  pt := ModuleCat.of R ↥(⨆ i, S i : Submodule R M)
  ι :=
    { app i := ModuleCat.ofHom (Submodule.inclusion (le_iSup S i))
      naturality i j f := by
        apply ModuleCat.hom_ext
        ext x
        rfl }

/-- The cocone map is literally inclusion on underlying values. -/
lemma inclusion_val (S : ι → Submodule R M) (hS : Monotone S) (i : ι) (x : S i) :
    (((cocone S hS).ι.app i).hom x).val = x.val := rfl

section Directed

variable [Nonempty ι] [IsDirectedOrder ι]

/-- Native filtered types certify the actual union point, even for a larger index universe. -/
def typesIsColimit (S : ι → Submodule R M) (hS : Monotone S) :
    IsColimit ((forget (ModuleCat.{v} R)).mapCocone (cocone S hS)) := by
  refine Types.FilteredColimit.isColimitOf'
    (J := ι) (F := diagram S hS ⋙ forget (ModuleCat.{v} R))
    (t := (forget (ModuleCat.{v} R)).mapCocone (cocone S hS)) ?_ ?_
  · intro x
    obtain ⟨i, hx⟩ := (Submodule.mem_iSup_of_directed S hS.directed_le).mp x.property
    exact ⟨i, ⟨x.val, hx⟩, rfl⟩
  · intro i x y h
    change (Submodule.inclusion (le_iSup S i) x : ↥(⨆ j, S j : Submodule R M)) =
      (Submodule.inclusion (le_iSup S i) y : ↥(⨆ j, S j : Submodule R M)) at h
    have hv : x.val = y.val :=
      congrArg (fun z : ↥(⨆ j, S j : Submodule R M) => z.val) h
    have he : x = y := Subtype.ext hv
    exact ⟨i, 𝟙 i, congrArg
      (fun z => ((diagram S hS ⋙ forget (ModuleCat.{v} R)).map (𝟙 i)) z) he⟩

/-- The universal function is the native type-colimit descent, not a new chosen engine. -/
def descFunction (S : ι → Submodule R M) (hS : Monotone S)
    (s : Cocone (diagram S hS)) : ↥(⨆ i, S i : Submodule R M) → s.pt :=
  (typesIsColimit S hS).desc ((forget (ModuleCat.{v} R)).mapCocone s)

/-- Native descent evaluates to the original cocone map on every stage. -/
lemma descFunction_inclusion (S : ι → Submodule R M) (hS : Monotone S)
    (s : Cocone (diagram S hS)) (i : ι) (x : S i) :
    descFunction S hS s (Submodule.inclusion (le_iSup S i) x) = (s.ι.app i).hom x :=
  congrArg (fun f => f x) ((typesIsColimit S hS).fac
    ((forget (ModuleCat.{v} R)).mapCocone s) i)

/-- Actual common stages and their linear cocone maps make native descent linear. -/
def descLinear (S : ι → Submodule R M) (hS : Monotone S)
    (s : Cocone (diagram S hS)) : ↥(⨆ i, S i : Submodule R M) →ₗ[R] s.pt where
  toFun := descFunction S hS s
  map_add' x y := by
    obtain ⟨i, xi, yi, hx, hy⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ (typesIsColimit S hS) x y
    have hx' : Submodule.inclusion (le_iSup S i) xi = x := hx
    have hy' : Submodule.inclusion (le_iSup S i) yi = y := hy
    rw [← hx', ← hy']
    let k := Submodule.inclusion (le_iSup S i)
    calc
      descFunction S hS s (k xi + k yi) = descFunction S hS s (k (xi + yi)) :=
        congrArg (descFunction S hS s) (map_add k xi yi).symm
      _ = (s.ι.app i).hom (xi + yi) := descFunction_inclusion S hS s i _
      _ = (s.ι.app i).hom xi + (s.ι.app i).hom yi := map_add _ _ _
      _ = descFunction S hS s (k xi) + descFunction S hS s (k yi) :=
        congrArg₂ (fun a b : s.pt => a + b)
          (descFunction_inclusion S hS s i xi).symm
          (descFunction_inclusion S hS s i yi).symm
  map_smul' r x := by
    obtain ⟨i, hx⟩ := (Submodule.mem_iSup_of_directed S hS.directed_le).mp x.property
    let xi : S i := ⟨x.val, hx⟩
    let k := Submodule.inclusion (le_iSup S i)
    have he : k xi = x := Subtype.ext rfl
    rw [← he]
    calc
      descFunction S hS s (r • k xi) = descFunction S hS s (k (r • xi)) :=
        congrArg (descFunction S hS s) (map_smul k r xi).symm
      _ = (s.ι.app i).hom (r • xi) := descFunction_inclusion S hS s i _
      _ = r • (s.ι.app i).hom xi := map_smul _ _ _
      _ = r • descFunction S hS s (k xi) :=
        congrArg (fun y => r • y) (descFunction_inclusion S hS s i xi).symm

/-- The native supremum cocone has the actual module-category universal property. -/
def isColimit (S : ι → Submodule R M) (hS : Monotone S) : IsColimit (cocone S hS) where
  desc s := ModuleCat.ofHom (descLinear S hS s)
  fac s i := by
    apply ModuleCat.hom_ext
    ext x
    exact descFunction_inclusion S hS s i x
  uniq s m hm := by
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨i, hx⟩ := (Submodule.mem_iSup_of_directed S hS.directed_le).mp x.property
    let xi : S i := ⟨x.val, hx⟩
    have he : Submodule.inclusion (le_iSup S i) xi = x := Subtype.ext rfl
    rw [← he]
    have h := congrArg (fun f : ModuleCat.of R (S i) ⟶ s.pt => f.hom xi) (hm i)
    exact h.trans (descFunction_inclusion S hS s i xi).symm

/-- This particular diagram has a colimit without a universal category-size premise. -/
instance hasColimit (S : ι → Submodule R M) (hS : Monotone S) :
    HasColimit (diagram S hS) := ⟨_, isColimit S hS⟩

section Coefficients

variable {N : Type v} [AddCommGroup N] [Module R N]

/-- Coefficient maps restrict to stages by their actual membership preservation. -/
def stageMap (S : ι → Submodule R M) (T : ι → Submodule R N)
    (f : M →ₗ[R] N) (hf : ∀ i x, x ∈ S i → f x ∈ T i) (i : ι) : S i →ₗ[R] T i :=
  (f.domRestrict (S i)).codRestrict (T i) (fun x => hf i x.val x.property)

/-- The induced union map is the original coefficient map on every value. -/
def iSupMap (S : ι → Submodule R M) (hS : Monotone S) (T : ι → Submodule R N)
    (f : M →ₗ[R] N) (hf : ∀ i x, x ∈ S i → f x ∈ T i) : ↥(⨆ i, S i : Submodule R M) →ₗ[R] ↥(⨆ i, T i : Submodule R N) :=
  (f.domRestrict (⨆ i, S i : Submodule R M)).codRestrict (⨆ i, T i : Submodule R N) (fun x => by
    obtain ⟨i, hx⟩ := (Submodule.mem_iSup_of_directed S hS.directed_le).mp x.property
    exact Submodule.mem_iSup_of_mem i (hf i x.val hx))

/-- No coefficient-map value changes in the union construction. -/
lemma iSupMap_val (S : ι → Submodule R M) (hS : Monotone S) (T : ι → Submodule R N)
    (f : M →ₗ[R] N) (hf : ∀ i x, x ∈ S i → f x ∈ T i) (x : ↥(⨆ i, S i : Submodule R M)) :
    (iSupMap S hS T f hf x).val = f x.val := rfl

/-- The actual restricted coefficient maps commute with all index inclusions. -/
def coefficientDiagramMap (S : ι → Submodule R M) (hS : Monotone S)
    (T : ι → Submodule R N) (hT : Monotone T) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ S i → f x ∈ T i) : diagram S hS ⟶ diagram T hT where
  app i := ModuleCat.ofHom (stageMap S T f hf i)
  naturality i j g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Coefficient and index maps give the actual union-cocone square. -/
lemma inclusion_coefficient (S : ι → Submodule R M) (hS : Monotone S)
    (T : ι → Submodule R N) (hT : Monotone T) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ S i → f x ∈ T i) (i : ι) :
    (cocone S hS).ι.app i ≫ ModuleCat.ofHom (iSupMap S hS T f hf) =
      (coefficientDiagramMap S hS T hT f hf).app i ≫ (cocone T hT).ι.app i := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Universal descent is precisely the actual coefficient map on the union. -/
lemma desc_coefficient (S : ι → Submodule R M) (hS : Monotone S)
    (T : ι → Submodule R N) (hT : Monotone T) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ S i → f x ∈ T i) :
    (isColimit S hS).desc ((Cocone.precompose
      (coefficientDiagramMap S hS T hT f hf)).obj (cocone T hT)) = ModuleCat.ofHom (iSupMap S hS T f hf) := by
  apply (isColimit S hS).hom_ext
  intro i
  exact ((isColimit S hS).fac _ i).trans
    (inclusion_coefficient S hS T hT f hf i).symm

end Coefficients
end Directed
end ModuleCat.DirectedSubmoduleColimit
