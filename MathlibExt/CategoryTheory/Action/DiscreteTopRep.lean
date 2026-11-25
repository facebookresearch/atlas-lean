/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.Action.DiscreteAbelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoinducedDiscreteAction
public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.Topology.CompactOpen

/-! # Original discrete abelian actions as topological representations -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v w

namespace CategoryTheory.DiscreteAbelianAction

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Retain the exact stored coefficient module and action through the stock equivalence. -/
abbrev toTopRep : DiscreteAbelianAction.{u, v} G ⥤ TopRep.{v, 0, u} ℤ G where
  obj M := (TopRep.fromActionTopModFunc (k := ℤ) (G := G)).obj M.obj.obj
  map f := (TopRep.fromActionTopModFunc (k := ℤ) (G := G)).map f.hom.hom
  map_id M := by
    change (TopRep.fromActionTopModFunc (k := ℤ) (G := G)).map (𝟙 M.obj.obj) = _
    exact Functor.map_id _ _
  map_comp f g := by
    change (TopRep.fromActionTopModFunc (k := ℤ) (G := G)).map
      (f.hom.hom ≫ g.hom.hom) = _
    exact Functor.map_comp _ _ _

/-- Every original coefficient carrier is retained literally. -/
theorem toTopRep_obj (M : DiscreteAbelianAction.{u, v} G) :
    ((toTopRep.obj M).V : Type v) = underlying M := rfl

/-- The topological representation has the original action on every vector. -/
theorem toTopRep_action (M : DiscreteAbelianAction.{u, v} G) (g : G) (m : underlying M) :
    (toTopRep.obj M).ρ g m = g • m := rfl

/-- Every stored equivariant integer-linear map has its original additive function. -/
theorem toTopRep_map_apply {M N : DiscreteAbelianAction.{u, v} G}
    (f : M ⟶ N) (m : underlying M) :
    (toTopRep.map f).hom m = homToAdd f m := rfl

instance toTopRep_faithful : (toTopRep.{u, v} (G := G)).Faithful where
  map_injective h := by
    apply (forget G).map_injective
    ext m
    exact congrArg (fun f => f.hom m) h

/-- Lift every actual TopRep arrow through the two full subcategories. -/
def ofTopRepHom {M N : DiscreteAbelianAction.{u, v} G}
    (f : toTopRep.obj M ⟶ toTopRep.obj N) : M ⟶ N :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ((TopRep.fromActionTopModFunc (k := ℤ) (G := G)).preimage f))

theorem toTopRep_map_ofTopRepHom {M N : DiscreteAbelianAction.{u, v} G}
    (f : toTopRep.obj M ⟶ toTopRep.obj N) : toTopRep.map (ofTopRepHom f) = f := by
  change (TopRep.fromActionTopModFunc (k := ℤ) (G := G)).map
    ((TopRep.fromActionTopModFunc (k := ℤ) (G := G)).preimage f) = f
  exact Functor.map_preimage _ _

instance toTopRep_full : (toTopRep.{u, v} (G := G)).Full where
  map_surjective f := ⟨ofTopRepHom f, toTopRep_map_ofTopRepHom f⟩

theorem ofTopRepHom_toTopRep_map {M N : DiscreteAbelianAction.{u, v} G}
    (f : M ⟶ N) : ofTopRepHom (toTopRep.map f) = f := by
  apply toTopRep.map_injective
  exact toTopRep_map_ofTopRepHom _

/-- The original joint continuity is retained by the same TopRep packaging. -/
theorem toTopRep_action_isContinuous (M : DiscreteAbelianAction.{u, v} G) :
    ((TopRep.toActionTopModFunc (k := ℤ) (G := G)).obj (toTopRep.obj M)).IsContinuous := by
  change M.obj.obj.IsContinuous
  exact M.obj.property

instance toTopRep_discrete (M : DiscreteAbelianAction.{u, v} G) :
    DiscreteTopology (toTopRep.obj M) := M.property

section Coinduction

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Actual compact-open coinduction in the same discrete continuous action category. -/
abbrev coind : DiscreteAbelianAction.{u, max u w} G ⥤
    DiscreteAbelianAction.{u, max u w} G where
  obj M :=
    ⟨⟨(TopRep.toActionTopModFunc (k := ℤ) (G := G)).obj (toTopRep.obj M).coind₁,
      ContinuousCohomology.coinduced_action_isContinuous
        (toTopRep.obj M) (toTopRep_action_isContinuous M)⟩,
      ContinuousCohomology.coinduced_discrete (toTopRep.obj M)⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    ((TopRep.toActionTopModFunc (k := ℤ) (G := G)).map
      ((TopRep.coind₁Functor ℤ G).map (toTopRep.map f))))
  map_id M := by
    apply (forget G).map_injective
    ext F
    rfl
  map_comp f g := by
    apply (forget G).map_injective
    ext F
    rfl

/-- The carrier is precisely the original continuous function module. -/
theorem coind_obj (M : DiscreteAbelianAction.{u, max u w} G) :
    (underlying (coind.{u, w}.obj M) : Type (max u w)) = C(G, underlying M) := rfl

/-- The literal continuous function carried by the actual coinduced object. -/
abbrev coindFunction (M : DiscreteAbelianAction.{u, max u w} G)
    (F : underlying (coind.{u, w}.obj M)) : C(G, underlying M) :=
  cast (coind_obj.{u, w} M) F

/-- Every original diagonal action value is retained through the stored action map. -/
theorem coind_action_apply (M : DiscreteAbelianAction.{u, max u w} G)
    (g x : G) (F : underlying (coind.{u, w}.obj M)) :
    coindFunction.{u, w} M (((coind.{u, w}.obj M).obj.obj.ρ g).asHom.hom F) x =
      (M.obj.obj.ρ g).asHom.hom (coindFunction.{u, w} M F (g⁻¹ * x)) := rfl

/-- Every coefficient arrow acts by the original postcomposition. -/
theorem coind_map_apply {M N : DiscreteAbelianAction.{u, max u w} G}
    (f : M ⟶ N) (F : underlying (coind.{u, w}.obj M)) (x : G) :
    coindFunction.{u, w} N (homToAdd (coind.{u, w}.map f) F) x =
      homToAdd f (coindFunction.{u, w} M F x) := rfl

/-- The actual equivariant constant-function inclusion. -/
def coindIota : 𝟭 (DiscreteAbelianAction.{u, max u w} G) ⟶ coind where
  app M := ObjectProperty.homMk (ObjectProperty.homMk
    ((TopRep.toActionTopModFunc (k := ℤ) (G := G)).map
      (TopRep.coind₁ι.app (toTopRep.obj M))))
  naturality {M N} f := by
    apply (forget G).map_injective
    ext m
    rfl

theorem coindIota_apply (M : DiscreteAbelianAction.{u, max u w} G)
    (m : underlying M) (x : G) :
    coindFunction.{u, w} M (homToAdd (coindIota.{u, w}.app M) m) x = m := rfl

/-- Evaluation at the identity on the exact stored additive modules. -/
def coindEvalOne (M : DiscreteAbelianAction.{u, max u w} G) :
    underlying (coind.{u, w}.obj M) →L[ℤ] underlying M := by
  let : DiscreteTopology (underlying (coind.{u, w}.obj M)) := (coind.{u, w}.obj M).property
  exact addHomContinuousLinearMap (underlying (coind.{u, w}.obj M)) (underlying M)
    { toFun := fun F => coindFunction.{u, w} M F 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem coindEvalOne_apply (M : DiscreteAbelianAction.{u, max u w} G)
    (F : underlying (coind.{u, w}.obj M)) :
    coindEvalOne.{u, w} M F = coindFunction.{u, w} M F 1 := rfl

/-- The original inclusion followed by underlying evaluation is the identity. -/
theorem coindEvalOne_iota (M : DiscreteAbelianAction.{u, max u w} G)
    (m : underlying M) : coindEvalOne.{u, w} M (homToAdd (coindIota.{u, w}.app M) m) = m := rfl

/-- The constant inclusion is mono, proved by its actual identity evaluation. -/
instance coindIota_mono (M : DiscreteAbelianAction.{u, max u w} G) :
    Mono (coindIota.{u, w}.app M) := by
  have hm : Mono ((forget G).map (coindIota.{u, w}.app M)) := by
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro x y h
    change homToAdd (coindIota.{u, w}.app M) x =
      homToAdd (coindIota.{u, w}.app M) y at h
    have hh := congrArg (fun F => coindEvalOne.{u, w} M F) h
    exact (coindEvalOne_iota.{u, w} M x).symm.trans
      (hh.trans (coindEvalOne_iota.{u, w} M y))
  exact (forget G).mono_of_mono_map hm

end Coinduction

end CategoryTheory.DiscreteAbelianAction
