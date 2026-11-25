/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/DayConvolution/Module.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.Mod
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Monoid

/-!
# Structure maps of modules for Day convolution

For monoidal categories `C` and `V`, the action of a monoid `M` in `C ⊛⥤ V` on a module `X`
restricts along the Day convolution units to natural maps
`M p ⊗ X q ⟶ X (p ⊗ q)`. A morphism of Day functors is a module morphism exactly when it
commutes with these structure maps, by the universal property of Day convolution.

When `M` comes from a lax monoidal functor through `DayFunctor.monObj`, its unit and tensorator
give the unit and iteration laws of the structure maps. For the sphere symmetric sequence these
are the equivariant iterated structure maps of a symmetric spectrum. Conversely, natural maps
`M p ⊗ G q ⟶ G (p ⊗ q)` satisfying these two laws are the structure maps of a unique module
structure on `G` (`Mod.dayMk`); this is how modules over Day convolution monoids, such as the
Eilenberg–MacLane spectra of modules, are built from their levels. Restricting scalars along a
monoid morphism precomposes the structure maps with it.

The proofs restrict Mathlib's internal-module laws along the units of the Day convolution
constructed by Robin Carlier, using the computation and extensionality lemmas in
`MathlibExt.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Basic`.

## Main definitions

* `Mod.dayStructureMap`: the levelwise action of a Day convolution module.
* `Mod.dayHomMk`: construct a module morphism from compatibility with the structure maps.
* `Mod.dayMk`: construct a module over the monoid of a lax monoidal functor from structure maps
  satisfying the unit and iteration laws.

## Main statements

* `Mod.dayStructureMap_naturality`: naturality in both variables.
* `Mod.dayStructureMap_hom`, `Mod.isModHom_iff_dayStructureMap`: the structure-map criterion for
  module morphisms.
* `Mod.dayStructureMap_comap`: the structure maps of a restriction of scalars.
* `Mod.dayStructureMap_unit`, `Mod.dayStructureMap_assoc`: the unit and iteration laws for modules
  over the monoid of a lax monoidal functor.
* `Mod.dayStructureMap_dayMk`: the structure maps of `Mod.dayMk` are the given maps.

## References

* B. Day, *On closed categories of functors*, Reports of the Midwest Category Seminar IV,
  Lecture Notes in Math. 137 (1970), 1-38.
* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory
open scoped DayFunctor ExternalProduct

namespace CategoryTheory.Mod

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

variable {M : C ⊛⥤ V} [MonObj M]

/-- The levelwise action `M p ⊗ X q ⟶ X (p ⊗ q)`, obtained by restricting the
module action along the Day convolution unit. -/
def dayStructureMap (X : Mod (C ⊛⥤ V) M) (p q : C) :
    M.functor.obj p ⊗ X.X.functor.obj q ⟶
      X.X.functor.obj (p ⊗ q) :=
  (DayFunctor.η M X.X).app (p, q) ≫
    (ModObj.smul (M := M) (X := X.X)).natTrans.app (p ⊗ q)

/-- The structure maps restrict the module action along the Day convolution units. -/
lemma dayStructureMap_def (X : Mod (C ⊛⥤ V) M) (p q : C) :
    X.dayStructureMap p q = (DayFunctor.η M X.X).app (p, q) ≫
      (ModObj.smul (M := M) (X := X.X)).natTrans.app (p ⊗ q) := (rfl)

/-- Naturality of the structure maps in both variables. -/
@[reassoc]
lemma dayStructureMap_naturality (X : Mod (C ⊛⥤ V) M) {p p' q q' : C}
    (f : p ⟶ p') (g : q ⟶ q') :
    (M.functor.map f ⊗ₘ X.X.functor.map g) ≫ X.dayStructureMap p' q' =
      X.dayStructureMap p q ≫ X.X.functor.map (f ⊗ₘ g) := by
  let τ := DayFunctor.η M X.X ≫
    Functor.whiskerLeft (tensor C)
      (ModObj.smul (M := M) (X := X.X)).natTrans
  simpa only [τ, NatTrans.comp_app, Functor.whiskerLeft_app,
    externalProductBifunctor_obj_map, Functor.comp_map, tensor_map, tensor_obj,
    tensorHom_def, dayStructureMap] using
    τ.naturality (CategoryTheory.Prod.mkHom f g)

/-- Every module morphism commutes with the structure maps. -/
@[reassoc (attr := simp)]
lemma dayStructureMap_hom {X Y : Mod (C ⊛⥤ V) M} (f : X ⟶ Y) (p q : C) :
    X.dayStructureMap p q ≫ f.hom.natTrans.app (p ⊗ q) =
      M.functor.obj p ◁ f.hom.natTrans.app q ≫
        Y.dayStructureMap p q := by
  have h := congrArg (fun g : M ⊗ X.X ⟶ Y.X ↦
    (DayFunctor.η M X.X).app (p, q) ≫ g.natTrans.app (p ⊗ q))
    (IsModHom.smul_hom (A := M) (f := f.hom))
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at h
  simpa [dayStructureMap] using h

/-- A morphism of Day functors is a module morphism exactly when it commutes with
the structure maps at every pair of objects. -/
lemma isModHom_iff_dayStructureMap {X Y : Mod (C ⊛⥤ V) M} (f : X.X ⟶ Y.X) :
    IsModHom M f ↔
      ∀ p q, X.dayStructureMap p q ≫ f.natTrans.app (p ⊗ q) =
        M.functor.obj p ◁ f.natTrans.app q ≫ Y.dayStructureMap p q := by
  constructor
  · intro h
    exact dayStructureMap_hom (⟨f⟩ : X ⟶ Y)
  · intro h
    constructor
    apply DayFunctor.tensor_hom_ext
    intro p q
    simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app, tensor_obj, Category.assoc,
      selfLeftAction_actionHomRight,
      DayFunctor.η_app_comp_whiskerLeft_natTrans_app_assoc, dayStructureMap] using h p q

/-- Construct a module morphism from a morphism of Day functors and its compatibility
with the structure maps. -/
def dayHomMk {X Y : Mod (C ⊛⥤ V) M} (f : X.X ⟶ Y.X)
    (h : ∀ p q, X.dayStructureMap p q ≫ f.natTrans.app (p ⊗ q) =
      M.functor.obj p ◁ f.natTrans.app q ≫ Y.dayStructureMap p q) :
    X ⟶ Y :=
  letI := (isModHom_iff_dayStructureMap f).mpr h
  ⟨f⟩

@[simp]
lemma dayHomMk_hom {X Y : Mod (C ⊛⥤ V) M} (f : X.X ⟶ Y.X)
    (h : ∀ p q, X.dayStructureMap p q ≫ f.natTrans.app (p ⊗ q) =
      M.functor.obj p ◁ f.natTrans.app q ≫ Y.dayStructureMap p q) :
    (dayHomMk f h).hom = f := (rfl)

/-- Restricting scalars along a monoid morphism `f : M ⟶ N` precomposes the structure maps with
`f`. -/
lemma dayStructureMap_comap {N : C ⊛⥤ V} [MonObj N] (f : M ⟶ N) [IsMonHom f]
    (X : Mod (C ⊛⥤ V) N) (p q : C) :
    ((comap f).obj X).dayStructureMap p q =
      f.natTrans.app p ▷ X.X.functor.obj q ≫ X.dayStructureMap p q := by
  rw [dayStructureMap_def, dayStructureMap_def]
  -- The action on the restriction is `f ▷ X ≫ γ[N, X]`, which unfolds from `scalarRestriction`.
  exact DayFunctor.η_app_comp_whiskerRight_natTrans_app_assoc f X.X p q _

section LaxMonoidal

variable {F : C ⊛⥤ V} [F.functor.LaxMonoidal]

/-- Acting by the monoidal unit, after its image under the lax monoidal unit map,
is the left unitor followed by the canonical reindexing. -/
-- Simplify before a concrete lax monoidal unit normalizes to its presentation.
@[reassoc (attr := simp↓)]
lemma dayStructureMap_unit (X : Mod (C ⊛⥤ V) F) (q : C) :
    Functor.LaxMonoidal.ε F.functor ▷ X.X.functor.obj q ≫
        X.dayStructureMap (𝟙_ C) q =
      (λ_ (X.X.functor.obj q)).hom ≫ X.X.functor.map (λ_ q).inv := by
  have h := congrArg (fun f : 𝟙_ (C ⊛⥤ V) ⊗ X.X ⟶ X.X ↦
    DayFunctor.ν C V ▷ X.X.functor.obj q ≫
      (DayFunctor.η (𝟙_ (C ⊛⥤ V)) X.X).app (𝟙_ C, q) ≫
      f.natTrans.app (𝟙_ C ⊗ q))
    (ModObj.one_smul_self F X.X)
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at h
  simpa [dayStructureMap, ← comp_whiskerRight_assoc] using h

/-- Multiplying before acting agrees with two successive structure maps. The final
reindexing records the associator of the source category. -/
@[reassoc]
lemma dayStructureMap_assoc (X : Mod (C ⊛⥤ V) F) (p q r : C) :
    Functor.LaxMonoidal.μ F.functor p q ▷ X.X.functor.obj r ≫
        X.dayStructureMap (p ⊗ q) r =
      (α_ _ _ _).hom ≫ F.functor.obj p ◁ X.dayStructureMap q r ≫
        X.dayStructureMap p (q ⊗ r) ≫ X.X.functor.map (α_ p q r).inv := by
  have h := congrArg
    (fun f : (F ⊗ F) ⊗ X.X ⟶ X.X ↦
      (DayFunctor.η F F).app (p, q) ▷
        X.X.functor.obj r ≫
      (DayFunctor.η (F ⊗ F) X.X).app
        (p ⊗ q, r) ≫ f.natTrans.app ((p ⊗ q) ⊗ r))
    (ModObj.mul_smul_self F X.X)
  simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app, tensor_obj, Category.assoc,
    selfLeftAction_actionHomRight,
    DayFunctor.η_app_comp_whiskerRight_natTrans_app_assoc,
    DayFunctor.η_app_comp_whiskerLeft_natTrans_app_assoc,
    DayFunctor.η_app_whiskerRight_comp_η_app_comp_associator_hom_natTrans_app_assoc,
    ← comp_whiskerRight_assoc, DayFunctor.η_app_comp_mul_natTrans_app,
    whiskerLeft_comp, dayStructureMap, NatTrans.naturality, NatTrans.naturality_assoc] using h

/-- The module over the Day convolution monoid of a lax monoidal functor `F` given by a Day
functor `G` and natural structure maps `a : F p ⊗ G q ⟶ G (p ⊗ q)` satisfying the unit and
iteration laws of `dayStructureMap_unit` and `dayStructureMap_assoc`. Its structure maps are `a`
(`dayStructureMap_dayMk`). -/
-- An abbreviation, so that the underlying Day functor of `dayMk G a unit assoc` is `G` up to
-- reducible unfolding, as the statement of `dayStructureMap_dayMk` and the levels of concrete
-- modules built with it require.
abbrev dayMk (G : C ⊛⥤ V) (a : F.functor ⊠ G.functor ⟶ tensor C ⋙ G.functor)
    (unit : ∀ q, Functor.LaxMonoidal.ε F.functor ▷ G.functor.obj q ≫ a.app (𝟙_ C, q) =
      (λ_ (G.functor.obj q)).hom ≫ G.functor.map (λ_ q).inv)
    (assoc : ∀ p q r, Functor.LaxMonoidal.μ F.functor p q ▷ G.functor.obj r ≫
        a.app (p ⊗ q, r) =
      (α_ _ _ _).hom ≫ F.functor.obj p ◁ a.app (q, r) ≫ a.app (p, q ⊗ r) ≫
        G.functor.map (α_ p q r).inv) :
    Mod (C ⊛⥤ V) F where
  X := G
  mod :=
    { smul := DayFunctor.tensorDesc a
      one_smul := DayFunctor.unit_tensor_hom_ext fun q ↦ by
        simpa [← comp_whiskerRight_assoc] using unit q
      mul_smul := DayFunctor.tensor_tensor_hom_ext fun p q r ↦ by
        simpa [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc] using assoc p q r }

/-- The structure maps of `dayMk G a unit assoc` are the given maps `a`. -/
@[simp]
lemma dayStructureMap_dayMk (G : C ⊛⥤ V) (a : F.functor ⊠ G.functor ⟶ tensor C ⋙ G.functor)
    (unit assoc) (p q : C) : (dayMk G a unit assoc).dayStructureMap p q = a.app (p, q) :=
  DayFunctor.η_comp_tensorDesc_app a p q

end LaxMonoidal

end

end CategoryTheory.Mod
