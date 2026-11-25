/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/

module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Eventual ranges of module diagrams

The native eventual ranges of a cofiltered Type-valued diagram are submodules
when its transition maps are linear. They form a module diagram, naturally in
the original diagram, with its canonical inclusion. Under the Mittag--Leffler
condition the restricted transitions are epimorphisms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {J : Type v} [Category.{t} J]

/-- The native eventual range at one object, with its inherited module structure. -/
def eventualRange (A : J ⥤ ModuleCat.{w} R) (j : J) : Submodule R (A.obj j) where
  carrier := (A ⋙ forget (ModuleCat.{w} R)).eventualRange j
  zero_mem' := by
    apply (Functor.mem_eventualRange_iff (A ⋙ forget (ModuleCat.{w} R))).mpr
    intro i f
    exact ⟨0, (A.map f).hom.map_zero⟩
  add_mem' := by
    intro x y hx hy
    apply (Functor.mem_eventualRange_iff (A ⋙ forget (ModuleCat.{w} R))).mpr
    intro i f
    obtain ⟨x', hx'⟩ := (Functor.mem_eventualRange_iff (A ⋙ forget (ModuleCat.{w} R))).mp hx f
    obtain ⟨y', hy'⟩ := (Functor.mem_eventualRange_iff (A ⋙ forget (ModuleCat.{w} R))).mp hy f
    change (A.map f).hom x' = x at hx'
    change (A.map f).hom y' = y at hy'
    refine ⟨x' + y', ?_⟩
    change (A.map f).hom (x' + y') = x + y
    rw [map_add, hx', hy']
  smul_mem' := by
    intro r x hx
    apply (Functor.mem_eventualRange_iff (A ⋙ forget (ModuleCat.{w} R))).mpr
    intro i f
    obtain ⟨x', hx'⟩ := (Functor.mem_eventualRange_iff (A ⋙ forget (ModuleCat.{w} R))).mp hx f
    change (A.map f).hom x' = x at hx'
    refine ⟨r • x', ?_⟩
    change (A.map f).hom (r • x') = r • x
    rw [map_smul, hx']

/-- Membership is the existing native eventual-range membership condition. -/
theorem mem_eventualRange_iff (A : J ⥤ ModuleCat.{w} R) (j : J) (x : A.obj j) :
    x ∈ eventualRange A j ↔
      x ∈ (A ⋙ forget (ModuleCat.{w} R)).eventualRange j :=
  Iff.rfl

variable [IsCofilteredOrEmpty J]

/-- Restrict a module diagram to its native eventual ranges. -/
def eventualRanges (A : J ⥤ ModuleCat.{w} R) : J ⥤ ModuleCat.{w} R where
  obj j := ModuleCat.of R (eventualRange A j)
  map f := ModuleCat.ofHom ((A.map f).hom.restrict
    (fun _ hx => (A ⋙ forget (ModuleCat.{w} R)).eventualRange_mapsTo f hx))
  map_id j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (A.map (𝟙 j)).hom (x : A.obj j) = (x : A.obj j)
    rw [A.map_id, ModuleCat.hom_id, LinearMap.id_apply]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (A.map (f ≫ g)).hom (x : A.obj _) =
      (A.map g).hom ((A.map f).hom (x : A.obj _))
    rw [A.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The restricted map has the same underlying value as the original transition. -/
@[simp]
theorem eventualRanges_map_val (A : J ⥤ ModuleCat.{w} R)
    {i j : J} (f : i ⟶ j) (x : eventualRange A i) :
    Subtype.val (show eventualRange A j from ((eventualRanges A).map f).hom x) =
      A.map f (x : A.obj i) :=
  rfl

/-- Forgetting the module lift gives the existing native Type-valued diagram. -/
def eventualRangesForgetIso (A : J ⥤ ModuleCat.{w} R) :
    eventualRanges A ⋙ forget (ModuleCat.{w} R) ≅
      (A ⋙ forget (ModuleCat.{w} R)).toEventualRanges :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro i j f
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

omit [IsCofilteredOrEmpty J] in
/-- Every map of module diagrams preserves the native eventual ranges. -/
theorem map_mem_eventualRange
    {A B : J ⥤ ModuleCat.{w} R} (α : A ⟶ B)
    {j : J} {x : A.obj j} (hx : x ∈ eventualRange A j) :
    (α.app j).hom x ∈ eventualRange B j := by
  apply (Functor.mem_eventualRange_iff (B ⋙ forget (ModuleCat.{w} R))).mpr
  intro i f
  obtain ⟨y, hy⟩ := (Functor.mem_eventualRange_iff (A ⋙ forget (ModuleCat.{w} R))).mp hx f
  change (A.map f).hom y = x at hy
  refine ⟨(α.app i).hom y, ?_⟩
  have h := ConcreteCategory.congr_hom (α.naturality f) y
  change (α.app j).hom ((A.map f).hom y) =
    (B.map f).hom ((α.app i).hom y) at h
  exact h.symm.trans (congrArg (α.app j).hom hy)

/-- A map of diagrams restricts to the corresponding eventual-range modules. -/
def eventualRangesMap {A B : J ⥤ ModuleCat.{w} R} (α : A ⟶ B) :
    eventualRanges A ⟶ eventualRanges B where
  app j := ModuleCat.ofHom ((α.app j).hom.restrict
    (fun _ hx => map_mem_eventualRange α hx))
  naturality i j f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (α.naturality f)
      ((show eventualRange A i from x) : A.obj i)

/-- Restricting a diagram map preserves its underlying component value. -/
@[simp]
theorem eventualRangesMap_app_val {A B : J ⥤ ModuleCat.{w} R}
    (α : A ⟶ B) (j : J) (x : eventualRange A j) :
    Subtype.val (show eventualRange B j from ((eventualRangesMap α).app j).hom x) =
      α.app j (x : A.obj j) :=
  rfl

/-- Eventual ranges are functorial in the module diagram. -/
def eventualRangesFunctor : (J ⥤ ModuleCat.{w} R) ⥤ (J ⥤ ModuleCat.{w} R) where
  obj := eventualRanges
  map := fun α => eventualRangesMap α
  map_id A := by
    apply NatTrans.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp α β := by
    apply NatTrans.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

/-- The canonical inclusion from eventual ranges into the original diagram. -/
def eventualRangesInclusion (A : J ⥤ ModuleCat.{w} R) : eventualRanges A ⟶ A where
  app j := ModuleCat.ofHom (eventualRange A j).subtype
  naturality i j f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Every component of the canonical inclusion is a monomorphism. -/
instance mono_eventualRangesInclusion_app (A : J ⥤ ModuleCat.{w} R) (j : J) :
    Mono ((eventualRangesInclusion A).app j) :=
  (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The canonical inclusion commutes with every map of module diagrams. -/
theorem eventualRangesInclusion_naturality
    {A B : J ⥤ ModuleCat.{w} R} (α : A ⟶ B) :
    eventualRangesMap α ≫ eventualRangesInclusion B =
      eventualRangesInclusion A ≫ α := by
  apply NatTrans.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The eventual-range inclusion is natural as the diagram varies. -/
def eventualRangesι : eventualRangesFunctor (R := R) (J := J) ⟶ 𝟭 _ where
  app := eventualRangesInclusion
  naturality _ _ α := eventualRangesInclusion_naturality α

/-- Under native Mittag--Leffler, the restricted transitions are epimorphisms. -/
theorem epi_eventualRanges_map (A : J ⥤ ModuleCat.{w} R)
    (hA : (A ⋙ forget (ModuleCat.{w} R)).IsMittagLeffler)
    {i j : J} (f : i ⟶ j) : Epi ((eventualRanges A).map f) :=
  (ModuleCat.epi_iff_surjective _).mpr
    ((A ⋙ forget (ModuleCat.{w} R)).surjective_toEventualRanges hA f)

section Limit

variable (A : J ⥤ ModuleCat.{w} R) [HasLimit A]

omit [IsCofilteredOrEmpty J] in
/-- Every actual limit projection lands in the native eventual range. -/
theorem limit_π_mem_eventualRange (j : J) (x : ↑(limit A)) :
    (limit.π A j).hom x ∈ eventualRange A j := by
  apply (Functor.mem_eventualRange_iff (A ⋙ forget (ModuleCat.{w} R))).mpr
  intro i f
  refine ⟨(limit.π A i).hom x, ?_⟩
  exact ConcreteCategory.congr_hom (limit.w A f) x

/-- Restrict the actual chosen limit cone to its eventual-range modules. -/
abbrev eventualRangesLimitCone : Cone (eventualRanges A) where
  pt := limit A
  π :=
    { app j := ModuleCat.ofHom ((limit.π A j).hom.codRestrict
        (eventualRange A j) (fun x => limit_π_mem_eventualRange A j x))
      naturality i j f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact (ConcreteCategory.congr_hom (limit.w A f) x).symm }

/-- Including a restricted cone projection gives the original limit projection. -/
theorem eventualRangesLimitCone_π_inclusion (j : J) :
    (eventualRangesLimitCone A).π.app j ≫ (eventualRangesInclusion A).app j =
      limit.π A j := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The cone with the original chosen limit as point is limiting after restriction. -/
def eventualRangesLimitConeIsLimit : IsLimit (eventualRangesLimitCone A) where
  lift S := limit.lift A ((Cone.postcompose (eventualRangesInclusion A)).obj S)
  fac S j := by
    apply (cancel_mono ((eventualRangesInclusion A).app j)).1
    rw [Category.assoc, eventualRangesLimitCone_π_inclusion, limit.lift_π]
    rfl
  uniq S m hm := by
    apply limit.hom_ext
    intro j
    have h := congrArg (fun f => f ≫ (eventualRangesInclusion A).app j) (hm j)
    rw [Category.assoc, eventualRangesLimitCone_π_inclusion] at h
    rw [limit.lift_π]
    exact h

/-- Eventual ranges have a limit whenever the original module diagram does. -/
instance (priority := low) hasLimit_eventualRanges : HasLimit (eventualRanges A) :=
  HasLimit.mk ⟨eventualRangesLimitCone A, eventualRangesLimitConeIsLimit A⟩

/-- The chosen eventual-range limit is canonically the original chosen limit. -/
def eventualRangesLimitIso : limit (eventualRanges A) ≅ limit A :=
  limit.isoLimitCone ⟨eventualRangesLimitCone A, eventualRangesLimitConeIsLimit A⟩

/-- Each coordinate of the comparison is the restricted projection followed by
the canonical stage inclusion. -/
@[reassoc]
theorem eventualRangesLimitIso_hom_π (j : J) :
    (eventualRangesLimitIso A).hom ≫ limit.π A j =
      limit.π (eventualRanges A) j ≫ (eventualRangesInclusion A).app j := by
  calc
    (eventualRangesLimitIso A).hom ≫ limit.π A j =
        (eventualRangesLimitIso A).hom ≫
          ((eventualRangesLimitCone A).π.app j ≫
            (eventualRangesInclusion A).app j) := by
      rw [eventualRangesLimitCone_π_inclusion]
    _ = ((eventualRangesLimitIso A).hom ≫ (eventualRangesLimitCone A).π.app j) ≫
        (eventualRangesInclusion A).app j := (Category.assoc _ _ _).symm
    _ = limit.π (eventualRanges A) j ≫ (eventualRangesInclusion A).app j := by
      apply congrArg (fun f => f ≫ (eventualRangesInclusion A).app j)
      exact limit.isoLimitCone_hom_π
        ⟨eventualRangesLimitCone A, eventualRangesLimitConeIsLimit A⟩ j

/-- The forward comparison map is the actual limit map of the canonical inclusion. -/
theorem eventualRangesLimitIso_hom :
    (eventualRangesLimitIso A).hom = limMap (eventualRangesInclusion A) := by
  apply limit.hom_ext
  intro j
  rw [eventualRangesLimitIso_hom_π, limMap_π]

end Limit

/-- The actual limit-inclusion isomorphisms are natural in the original diagram. -/
@[reassoc]
theorem eventualRangesLimitIso_naturality
    {A B : J ⥤ ModuleCat.{w} R} [HasLimit A] [HasLimit B] (α : A ⟶ B) :
    limMap (eventualRangesMap α) ≫ (eventualRangesLimitIso B).hom =
      (eventualRangesLimitIso A).hom ≫ limMap α := by
  apply limit.hom_ext
  intro j
  rw [Category.assoc, eventualRangesLimitIso_hom_π]
  rw [← Category.assoc, limMap_π, Category.assoc]
  rw [Category.assoc, limMap_π, eventualRangesLimitIso_hom_π_assoc]
  have h := NatTrans.congr_app (eventualRangesInclusion_naturality α) j
  exact congrArg (fun f => limit.π (eventualRanges A) j ≫ f) h

end ModuleCat
