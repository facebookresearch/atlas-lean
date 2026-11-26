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
# Eventual image submodules and their limits

For an R-module diagram A on a category J, the eventual range at j is the intersection of the
images of every incoming transition A_i → A_j. These subsets are R-submodules. For cofiltered-
or-empty J, the transitions restrict to a diagram of eventual range modules, naturally
included in A and functorial in maps of diagrams.

If the underlying-set diagram is Mittag–Leffler, the restricted transitions are epimorphisms.
Whenever A has a limit, its projections land in the eventual ranges, and the same limit object
gives a limit of the restricted diagram. The canonical isomorphism lim(eventualRanges A) ≅ lim
A is induced by the inclusion and is natural in A. The ring, index-object, index-morphism and
module universes are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {J : Type v} [Category.{t} J]

/-- The eventual image submodule at a diagram object.

For A : J → ModuleCat R, the eventual range at j consists of elements of A_j lying in the
image of A(f) for every arrow f : i → j. Linearity makes this intersection a submodule. -/
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

/-- Membership agrees with the underlying-set eventual range.

An element belongs to the module eventual range at j exactly when it belongs to the eventual
range of the diagram obtained by forgetting module structure. -/
theorem mem_eventualRange_iff (A : J ⥤ ModuleCat.{w} R) (j : J) (x : A.obj j) :
    x ∈ eventualRange A j ↔
      x ∈ (A ⋙ forget (ModuleCat.{w} R)).eventualRange j :=
  Iff.rfl

variable [IsCofilteredOrEmpty J]

/-- The diagram restricted to its eventual image submodules.

For cofiltered-or-empty J, take the eventual range module at each j and restrict each
transition map to these submodules. -/
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

/-- Values of the restricted eventual-image transition.

The transition between eventual range modules sends x to the same underlying element A(f)(x)
as the transition of A. -/
@[simp]
theorem eventualRanges_map_val (A : J ⥤ ModuleCat.{w} R)
    {i j : J} (f : i ⟶ j) (x : eventualRange A i) :
    Subtype.val (show eventualRange A j from ((eventualRanges A).map f).hom x) =
      A.map f (x : A.obj i) :=
  rfl

/-- The underlying-set diagram of eventual image modules.

Forgetting the R-module structures of eventualRanges A gives a diagram naturally isomorphic to
the underlying-set eventual range diagram, with identity components. -/
def eventualRangesForgetIso (A : J ⥤ ModuleCat.{w} R) :
    eventualRanges A ⋙ forget (ModuleCat.{w} R) ≅
      (A ⋙ forget (ModuleCat.{w} R)).toEventualRanges :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro i j f
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

omit [IsCofilteredOrEmpty J] in
/-- Natural transformations preserve eventual images.

For a natural transformation α : A → B of module diagrams, α_j sends every element of the
eventual range of A at j into that of B at j. -/
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

/-- The natural transformation restricted to eventual images.

Restrict the components of a diagram map α : A → B to obtain eventualRanges A → eventualRanges
B. -/
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

/-- Values of a restricted eventual-image diagram map.

The j-component of eventualRangesMap α sends an eventual-range element x to the underlying
element α_j(x). -/
@[simp]
theorem eventualRangesMap_app_val {A B : J ⥤ ModuleCat.{w} R}
    (α : A ⟶ B) (j : J) (x : eventualRange A j) :
    Subtype.val (show eventualRange B j from ((eventualRangesMap α).app j).hom x) =
      α.app j (x : A.obj j) :=
  rfl

/-- Functoriality of the eventual image construction.

Taking eventual range modules and restricting natural transformations defines an endofunctor
on module diagrams over a cofiltered-or-empty category J. -/
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

/-- The inclusion of the eventual image subdiagram.

At j, the inclusion eventualRanges A → A is the subtype inclusion of the eventual range
submodule into A_j. -/
def eventualRangesInclusion (A : J ⥤ ModuleCat.{w} R) : eventualRanges A ⟶ A where
  app j := ModuleCat.ofHom (eventualRange A j).subtype
  naturality i j f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The eventual image inclusion is componentwise monic.

Each component of eventualRangesInclusion A is a monomorphism, since it is an injective
submodule inclusion. -/
instance mono_eventualRangesInclusion_app (A : J ⥤ ModuleCat.{w} R) (j : J) :
    Mono ((eventualRangesInclusion A).app j) :=
  (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The inclusion square for maps of module diagrams.

For α : A → B, the restricted map followed by inclusion into B equals inclusion into A
followed by α. -/
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

/-- The natural inclusion of the eventual image endofunctor.

The inclusions of eventual ranges form a natural transformation from eventualRangesFunctor to
the identity on module diagrams. -/
def eventualRangesι : eventualRangesFunctor (R := R) (J := J) ⟶ 𝟭 _ where
  app := eventualRangesInclusion
  naturality _ _ α := eventualRangesInclusion_naturality α

/-- Mittag–Leffler eventual-image transitions are epimorphisms.

If the underlying-set diagram of A is Mittag–Leffler, every transition in eventualRanges A is
surjective and hence an epimorphism of R-modules. -/
theorem epi_eventualRanges_map (A : J ⥤ ModuleCat.{w} R)
    (hA : (A ⋙ forget (ModuleCat.{w} R)).IsMittagLeffler)
    {i j : J} (f : i ⟶ j) : Epi ((eventualRanges A).map f) :=
  (ModuleCat.epi_iff_surjective _).mpr
    ((A ⋙ forget (ModuleCat.{w} R)).surjective_toEventualRanges hA f)

section Limit

variable (A : J ⥤ ModuleCat.{w} R) [HasLimit A]

omit [IsCofilteredOrEmpty J] in
/-- Limit projections land in the eventual image submodules.

For any module diagram with a limit, each coordinate of a limit element belongs to the
eventual range at that coordinate. -/
theorem limit_π_mem_eventualRange (j : J) (x : ↑(limit A)) :
    (limit.π A j).hom x ∈ eventualRange A j := by
  apply (Functor.mem_eventualRange_iff (A ⋙ forget (ModuleCat.{w} R))).mpr
  intro i f
  refine ⟨(limit.π A i).hom x, ?_⟩
  exact ConcreteCategory.congr_hom (limit.w A f) x

/-- The limit cone restricted to eventual images.

Use lim A as cone point and restrict each chosen limit projection to the eventual range
submodule of its target. -/
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

/-- The restricted limit coordinates recover the full coordinates.

Each projection of eventualRangesLimitCone A followed by the eventual-range inclusion equals
the chosen projection lim A → A_j. -/
theorem eventualRangesLimitCone_π_inclusion (j : J) :
    (eventualRangesLimitCone A).π.app j ≫ (eventualRangesInclusion A).app j =
      limit.π A j := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The restricted cone retains the limit universal property.

For a cofiltered-or-empty module diagram A with a limit, the cone with point lim A and
eventual-range-valued projections is a limit cone of eventualRanges A. -/
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

/-- The limit comparison for eventual image modules.

The chosen limit of eventualRanges A is canonically isomorphic to lim A through the limiting
restricted cone. -/
def eventualRangesLimitIso : limit (eventualRanges A) ≅ limit A :=
  limit.isoLimitCone ⟨eventualRangesLimitCone A, eventualRangesLimitConeIsLimit A⟩

/-- Coordinates of the eventual-image limit isomorphism.

The forward comparison followed by the j-th projection of A equals the j-th projection of
eventualRanges A followed by its stage inclusion. -/
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

/-- The forward comparison is the limit map of the inclusion.

The forward morphism lim(eventualRanges A) → lim A equals limMap(eventualRangesInclusion A). -/
theorem eventualRangesLimitIso_hom :
    (eventualRangesLimitIso A).hom = limMap (eventualRangesInclusion A) := by
  apply limit.hom_ext
  intro j
  rw [eventualRangesLimitIso_hom_π, limMap_π]

end Limit

/-- Naturality of eventual-image limit comparison.

For α : A → B, the limit of its restricted eventual-range map followed by the comparison for B
equals the comparison for A followed by limMap α. -/
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
