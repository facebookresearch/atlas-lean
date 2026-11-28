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

/-!
# Discrete abelian actions and continuous representations

For a group G with a topology in universe u, a discrete continuous abelian G-action with
coefficient universe v defines a continuous ℤ-representation on the same coefficient group and
topology. The comparison functor J is full and faithful: equivariant continuous ℤ-linear maps
are exactly the morphisms between these actions.

When G is a compact, totally disconnected topological group, diagonal coinduction remains in the
discrete continuous action category at coefficient universe W=max(u,w). Its carrier is C(G,A),
its action is (h•F)(g)=h•F(h⁻¹g), and coefficient maps act by postcomposition. Constant
functions give a natural monomorphism A→C(G,A). Evaluation at 1 is a continuous ℤ-linear
retraction on the underlying coefficient modules; it need not be an equivariant action morphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v w

namespace CategoryTheory.DiscreteAbelianAction

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Let G be a group with a topology in universe u and let discrete continuous abelian coefficient
actions lie in universe v. The functor J sends A to the continuous ℤ-representation with the
same coefficient group, discrete topology, and G-action. It sends each action morphism to its
equivariant continuous ℤ-linear coefficient map, retaining coefficient universe v independently
of the group universe. -/
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

/-- Let G be a group with a topology in universe u and let discrete continuous abelian coefficient
actions lie in universe v. For J, the functor to continuous ℤ-representations, the coefficient
carrier of J(A) equals the underlying abelian group of A as a type in universe v. The group
operations, integer module structure, and topology are those of the same coefficient object. -/
theorem toTopRep_obj (M : DiscreteAbelianAction.{u, v} G) :
    ((toTopRep.obj M).V : Type v) = underlying M := rfl

/-- Let G be a group with a topology in universe u and let discrete continuous abelian coefficient
actions lie in universe v. For a coefficient action A, g∈G, and a∈A, the associated
representation J(A) has ρ_{J(A)}(g)(a)=g•a. Thus the representation and action descriptions have
the same coefficient action on every element. -/
theorem toTopRep_action (M : DiscreteAbelianAction.{u, v} G) (g : G) (m : underlying M) :
    (toTopRep.obj M).ρ g m = g • m := rfl

/-- Let G be a group with a topology in universe u and let discrete continuous abelian coefficient
actions lie in universe v. For an action morphism f:A→B and a∈A, the continuous ℤ-linear map
J(f) satisfies J(f)(a)=f(a), with f on the right regarded as its underlying additive coefficient
map. -/
theorem toTopRep_map_apply {M N : DiscreteAbelianAction.{u, v} G}
    (f : M ⟶ N) (m : underlying M) :
    (toTopRep.map f).hom m = homToAdd f m := rfl

instance toTopRep_faithful : (toTopRep.{u, v} (G := G)).Faithful where
  map_injective h := by
    apply (forget G).map_injective
    ext m
    exact congrArg (fun f => f.hom m) h

/-- Let G be a group with a topology in universe u and let discrete continuous abelian coefficient
actions lie in universe v. For A,B and a continuous equivariant ℤ-linear morphism f:J(A)→J(B),
there is an action morphism A→B with representation image f. The lifted morphism has the same
additive function and the same equivariance relation. -/
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

/-- Let G be a group with a topology in universe u and let discrete continuous abelian coefficient
actions lie in universe v. For every A, the action map G×J(A)→J(A), (g,a)↦ρ(g)(a), is jointly
continuous. This is the joint continuity of the given discrete coefficient action, with its
topology and coefficient module unchanged. -/
theorem toTopRep_action_isContinuous (M : DiscreteAbelianAction.{u, v} G) :
    ((TopRep.toActionTopModFunc (k := ℤ) (G := G)).obj (toTopRep.obj M)).IsContinuous := by
  change M.obj.obj.IsContinuous
  exact M.obj.property

instance toTopRep_discrete (M : DiscreteAbelianAction.{u, v} G) :
    DiscreteTopology (toTopRep.obj M) := M.property

section Coinduction

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Let G be a compact, totally disconnected topological group in universe u and let discrete
continuous abelian coefficients lie in W=max(u,w). The coinduction endofunctor C sends A to
C(G,A), with compact-open topology and action (h•F)(g)=h•F(h⁻¹g). This function group is
discrete and its action jointly continuous. A coefficient morphism f:A→B is sent to F↦f∘F. -/
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

/-- Let G be a compact, totally disconnected topological group in universe u and let discrete
continuous abelian coefficients lie in W=max(u,w). For the diagonal coinduction C A, its
underlying abelian-group carrier equals C(G,A) in universe W, the continuous functions from G to
the underlying coefficient group of A. Addition is pointwise and the topology is compact-open. -/
theorem coind_obj (M : DiscreteAbelianAction.{u, max u w} G) :
    (underlying (coind.{u, w}.obj M) : Type (max u w)) = C(G, underlying M) := rfl

/-- Let G be a compact, totally disconnected topological group in universe u and let discrete
continuous abelian coefficients lie in W=max(u,w). For A and F in the underlying carrier of C A,
the coefficient function F:G→A is its corresponding element of C(G,A), with the same pointwise
values. Both the coinduced carrier and continuous function space lie in W. -/
abbrev coindFunction (M : DiscreteAbelianAction.{u, max u w} G)
    (F : underlying (coind.{u, w}.obj M)) : C(G, underlying M) :=
  cast (coind_obj.{u, w} M) F

/-- Let G be a compact, totally disconnected topological group in universe u and let discrete
continuous abelian coefficients lie in W=max(u,w). For A, F∈C A, and h,x∈G, the diagonal
coinduction action satisfies (h•F)(x)=h•F(h⁻¹x). The first h acts on the coefficient A and h⁻¹x
is the translated function argument. -/
theorem coind_action_apply (M : DiscreteAbelianAction.{u, max u w} G)
    (g x : G) (F : underlying (coind.{u, w}.obj M)) :
    coindFunction.{u, w} M (((coind.{u, w}.obj M).obj.obj.ρ g).asHom.hom F) x =
      (M.obj.obj.ρ g).asHom.hom (coindFunction.{u, w} M F (g⁻¹ * x)) := rfl

/-- Let G be a compact, totally disconnected topological group in universe u and let discrete
continuous abelian coefficients lie in W=max(u,w). For an equivariant additive coefficient map
f:A→B, F∈C A, and x∈G, the induced coinduction map satisfies (C(f)(F))(x)=f(F(x)). This is
continuous postcomposition by the same coefficient morphism. -/
theorem coind_map_apply {M N : DiscreteAbelianAction.{u, max u w} G}
    (f : M ⟶ N) (F : underlying (coind.{u, w}.obj M)) (x : G) :
    coindFunction.{u, w} N (homToAdd (coind.{u, w}.map f) F) x =
      homToAdd f (coindFunction.{u, w} M F x) := rfl

/-- Let G be a compact, totally disconnected topological group in universe u and let discrete
continuous abelian coefficients lie in W=max(u,w). The natural transformation ι:Id→C has
component ι_A:A→C A given by ι_A(a)(g)=a. Each component is an equivariant additive action
morphism, and for f:A→B, f≫ι_B=ι_A≫C(f). -/
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

/-- Let G be a compact, totally disconnected topological group in universe u and let discrete
continuous abelian coefficients lie in W=max(u,w). For A, evaluation ε_A:C(G,A)→A, ε_A(F)=F(1),
is a continuous ℤ-linear map of underlying coefficient modules. This statement does not assert
equivariance; the domain and target carry their discrete coefficient topologies. -/
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

/-- Let G be a compact, totally disconnected topological group in universe u and let discrete
continuous abelian coefficients lie in W=max(u,w). For a coefficient action A and a∈A,
evaluation ε_A(F)=F(1) and the constant inclusion ι_A satisfy ε_A(ι_A(a))=a. Thus the inclusion
is split injective on the underlying continuous ℤ-modules. -/
theorem coindEvalOne_iota (M : DiscreteAbelianAction.{u, max u w} G)
    (m : underlying M) : coindEvalOne.{u, w} M (homToAdd (coindIota.{u, w}.app M) m) = m := rfl

/-- Let G be a compact, totally disconnected topological group in universe u and let discrete
continuous abelian coefficients lie in W=max(u,w). For every A, the action morphism ι_A:A→C A is
mono. Its underlying additive map is injective because identity evaluation ε_A retracts it, so
ι_A can be cancelled on the right in the action category. -/
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
