/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeMono
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoFunctorCategorical
public import
  MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-!
# Cobase change along monomorphisms into general quasicategories (the supporting results)

```text
(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u}).
```

Fix a pushout square `sq : IsPushout i f f' j` of simplicial sets
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}

/-! ## Pointwise evaluations and core membership (§1 of the header) -/

/-- **Vertex evaluations of an equivalence edge are equivalences.**
For an equivalence edge `e` of `Fun(A, C)` and a vertex map
`v : Δ[0] ⟶ A`, the edge of `C` obtained by precomposing with `v`
and evaluating at `Δ[0]` through `SSet.evalDeltaZeroIso` is an
equivalence in `C`. These are the pointwise equivalences that occur
as the special edges of the special outer horns in §2 of the
header. -/
theorem Edge.IsEquivalence.eval_vertex {C : SSet.{u}}
    {a₀ a₁ : ((ihom A).obj C) _⦋0⦌} {e : Edge a₀ a₁}
    (he : e.IsEquivalence) (v : (Δ[0] : SSet.{u}) ⟶ A) :
    ((e.map ((pre v).app C)).map (evalDeltaZeroIso C).hom).IsEquivalence :=
  (he.map ((pre v).app C)).map _

/-- An equivalence edge of `Fun(A, C)` is a `1`-simplex of the core
of the functor object: `e.edge ∈ core (Fun(A, C))` by
`SSet.mem_core_obj_one_iff`. This is the factorization that
`e.IsEquivalence` actually gives; it must not be confused with a
factorization of the endpoint vertices through `Fun(A, core C)`
(§1 of the header). -/
theorem Edge.IsEquivalence.mem_core_edge_ihom {C : SSet.{u}}
    {a₀ a₁ : ((ihom A).obj C) _⦋0⦌} {e : Edge a₀ a₁}
    (he : e.IsEquivalence) :
    e.edge ∈ (core ((ihom A).obj C)).obj (Opposite.op ⦋1⦌) :=
  mem_core_obj_one_iff.2 (he.of_edge_eq rfl)

/-- **Sub-claim (i) of §1.** If the vertex of `Fun(A, C)` classified
by `g : A ⟶ C` lifts along postcomposition with `(core C).ι` to a
vertex of `Fun(A, core C)`, then every `1`-simplex image
`g.app _ s` is an equivalence edge of `C`: the lift is classified
by a map `G : A ⟶ (core C : SSet)` with `G ≫ (core C).ι = g`
(`SSet.ihomVertexEquiv_ihom_map`), and membership of `G.app _ s`
in the core is `SSet.mem_core_obj_one_iff`. -/
theorem isEquivalence_mk'_app_of_ihomVertex_lift_core {C : SSet.{u}}
    {g : A ⟶ C}
    (hlift : ∃ bt : ((ihom A).obj (core C : SSet.{u})) _⦋0⦌,
      ((ihom A).map (core C).ι).app (Opposite.op ⦋0⦌) bt =
        ihomVertexEquiv A C g)
    (s : A _⦋1⦌) : (Edge.mk' (g.app (Opposite.op ⦋1⦌) s)).IsEquivalence := by
  obtain ⟨bt, hbt⟩ := hlift
  set G : A ⟶ (core C : SSet.{u}) :=
    (ihomVertexEquiv A (core C : SSet.{u})).symm bt with hG
  have hGg : G ≫ (core C).ι = g := by
    apply (ihomVertexEquiv A C).injective
    rw [← ihomVertexEquiv_ihom_map, hG, Equiv.apply_symm_apply]
    exact hbt
  have happ : g.app (Opposite.op ⦋1⦌) s = (G.app (Opposite.op ⦋1⦌) s).1 := by
    rw [← hGg]
    rfl
  rw [happ]
  exact mem_core_obj_one_iff.mp (G.app (Opposite.op ⦋1⦌) s).2

/-- **Failure of sub-claim (ii) of §1 (the core-route gap).** For
every non-equivalence edge `e₀` of `C` there is a vertex `b` of
`Fun(Δ[1], C)` — the one classifying `e₀` itself — such that the
identity edge at `b` is an equivalence of `Fun(Δ[1], C)` but `b`
does not lift along postcomposition with `(core C).ι` to
`Fun(Δ[1], core C)`: by
`SSet.isEquivalence_mk'_app_of_ihomVertex_lift_core` at the
fundamental simplex `yonedaEquiv (𝟙 Δ[1])`, a lift would make
`e₀` an equivalence. Hence the endpoint vertices in the lifting
problem (A) do not in general belong to `Fun(-, core C)`, and (A)
does not reduce to the Kan-target case of the supporting results at `core C`. -/
theorem exists_equivalence_edge_endpoint_not_lift_core {C : SSet.{u}}
    {x₀ x₁ : C _⦋0⦌} (e₀ : Edge x₀ x₁) (h₀ : ¬ e₀.IsEquivalence) :
    ∃ b : ((ihom (Δ[1] : SSet.{u})).obj C) _⦋0⦌,
      (Edge.id b).IsEquivalence ∧
        ¬ ∃ bt : ((ihom (Δ[1] : SSet.{u})).obj (core C : SSet.{u})) _⦋0⦌,
          ((ihom (Δ[1] : SSet.{u})).map (core C).ι).app (Opposite.op ⦋0⦌) bt = b := by
  refine ⟨ihomVertexEquiv (Δ[1] : SSet.{u}) C (yonedaEquiv.symm e₀.edge),
    Edge.isEquivalence_id _, fun hlift => h₀ ?_⟩
  have key := isEquivalence_mk'_app_of_ihomVertex_lift_core
    (g := yonedaEquiv.symm e₀.edge) hlift (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  have happ : (yonedaEquiv.symm e₀.edge).app (Opposite.op ⦋1⦌)
        (yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = e₀.edge :=
    yonedaEquiv_symm_app_id _
  rw [happ] at key
  exact key.of_edge_eq rfl

/-! ## Fullness of the cobase change (§3 of the header) -/

/-- The morphism represented by a transported edge: transporting
the endpoints along vertex equalities conjugates `toHoHom` by the
corresponding `eqToHom` morphisms. Proved by `subst` on abstract
vertices, where `Edge.ofEq` with `rfl` proofs is the original edge
(`SSet.Edge.ext`). -/
private lemma cobaseGen_toHoHom_ofEq {W : SSet.{u}} {a b a' b' : W _⦋0⦌}
    (e : Edge a b) (h₀ : a = a') (h₁ : b = b') :
    (e.ofEq h₀ h₁).toHoHom =
      eqToHom (congrArg HomotopyCategory.mk h₀.symm) ≫ e.toHoHom ≫
        eqToHom (congrArg HomotopyCategory.mk h₁) := by
  subst h₀
  subst h₁
  have hEq : e.ofEq rfl rfl = e := Edge.ext rfl
  rw [hEq]
  change e.toHoHom = eqToHom (rfl : HomotopyCategory.mk a =
    HomotopyCategory.mk a) ≫ e.toHoHom ≫
      eqToHom (rfl : HomotopyCategory.mk b = HomotopyCategory.mk b)
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- **Fullness of precomposition with a cobase change
(the additional comparison obligation(1), unconditional).** In a pushout square
`IsPushout i f f' j` with `i` a monomorphism and `f` a categorical
equivalence, precomposition with `f'` induces a full functor on
homotopy categories of functor objects into every quasicategory
`C`. The proof is §3 of the module header: represent the given
morphism by an edge of `Fun(B, C)`, take a preimage edge in
`Fun(X, C)` through the equivalence `hFun(f, C)`, correct the first
edge by `SSet.exists_edge_correction_of_innerFibration` (the supporting results, inner horn `Λ[2, 1]` through the inner fibration
`(pre i).app C`) so the two edges agree strictly in `Fun(A, C)`,
and glue along `SSet.isPullback_pre_app_of_isPushout` (the supporting results). -/
theorem hoFunctor_pre_full_of_isPushout
    (sq : IsPushout i f f' j) [Mono i] (hf : categoricalEquivalences f)
    (C : SSet.{u}) [Quasicategory C] :
    (hoFunctor.map ((pre f').app C)).toFunctor.Full := by
  have hFf : (hoFunctor.map ((pre f).app C)).toFunctor.IsEquivalence :=
    (categoricalEquivalences.mem_iff f).1 hf C inferInstance
  have hFf' : (mapHomotopyCategory ((pre f).app C)).IsEquivalence := hFf
  have := hFf'
  change (mapHomotopyCategory ((pre f').app C)).Full
  constructor
  intro P Q φ
  obtain ⟨y₁, rfl⟩ : ∃ y, HomotopyCategory.mk y = P :=
    ⟨_, HomotopyCategory.objEquiv.left_inv P⟩
  obtain ⟨y₂, rfl⟩ : ∃ y, HomotopyCategory.mk y = Q :=
    ⟨_, HomotopyCategory.objEquiv.left_inv Q⟩
  obtain ⟨uB, huB⟩ := Edge.exists_toHoHom_eq (show
    (HomotopyCategory.mk (((pre f').app C).app _ y₁) :
      hoFunctor.obj ((ihom B).obj C)) ⟶
      HomotopyCategory.mk (((pre f').app C).app _ y₂) from φ)
  have hv : ∀ y : ((ihom Y).obj C) _⦋0⦌,
      ((pre f).app C).app _ (((pre j).app C).app _ y) =
        ((pre i).app C).app _ (((pre f').app C).app _ y) := by
    intro y
    have key1 : (pre j).app C ≫ (pre f).app C = (pre (f ≫ j)).app C := by
      rw [pre_map]; rfl
    have key2 : (pre f').app C ≫ (pre i).app C = (pre (i ≫ f')).app C := by
      rw [pre_map]; rfl
    change (((pre j).app C ≫ (pre f).app C).app _ y) =
      (((pre f').app C ≫ (pre i).app C).app _ y)
    rw [key1, key2, sq.w]
  obtain ⟨ξ, hξ⟩ := (mapHomotopyCategory ((pre f).app C)).map_surjective
    (X := HomotopyCategory.mk (((pre j).app C).app _ y₁))
    (Y := HomotopyCategory.mk (((pre j).app C).app _ y₂))
    (eqToHom (congrArg HomotopyCategory.mk (hv y₁)) ≫
      (uB.map ((pre i).app C)).toHoHom ≫
        eqToHom (congrArg HomotopyCategory.mk (hv y₂).symm))
  obtain ⟨uX, huX⟩ := Edge.exists_toHoHom_eq ξ
  have hstep : (uX.map ((pre f).app C)).toHoHom =
      eqToHom (congrArg HomotopyCategory.mk (hv y₁)) ≫
        (uB.map ((pre i).app C)).toHoHom ≫
          eqToHom (congrArg HomotopyCategory.mk (hv y₂).symm) := by
    rw [Edge.toHoHom_map, huX]
    exact hξ
  have hcanc1 : eqToHom (congrArg HomotopyCategory.mk (hv y₁).symm) ≫
        eqToHom (congrArg HomotopyCategory.mk (hv y₁)) =
      𝟙 (HomotopyCategory.mk
        (((pre i).app C).app _ (((pre f').app C).app _ y₁))) := by
    rw [eqToHom_trans]
    change eqToHom (rfl : HomotopyCategory.mk
      (((pre i).app C).app _ (((pre f').app C).app _ y₁)) =
      HomotopyCategory.mk
        (((pre i).app C).app _ (((pre f').app C).app _ y₁))) = _
    rw [eqToHom_refl]
  have hcanc2 : eqToHom (congrArg HomotopyCategory.mk (hv y₂).symm) ≫
        eqToHom (congrArg HomotopyCategory.mk (hv y₂)) =
      𝟙 (HomotopyCategory.mk
        (((pre i).app C).app _ (((pre f').app C).app _ y₂))) := by
    rw [eqToHom_trans]
    change eqToHom (rfl : HomotopyCategory.mk
      (((pre i).app C).app _ (((pre f').app C).app _ y₂)) =
      HomotopyCategory.mk
        (((pre i).app C).app _ (((pre f').app C).app _ y₂))) = _
    rw [eqToHom_refl]
  have hw : ((uX.map ((pre f).app C)).ofEq (hv y₁) (hv y₂)).toHoHom =
      (uB.map ((pre i).app C)).toHoHom := by
    rw [cobaseGen_toHoHom_ofEq, hstep]
    simp only [← Category.assoc]
    rw [hcanc1, Category.id_comp, Category.assoc, hcanc2, Category.comp_id]
  obtain ⟨uB', huB'1, huB'2⟩ :=
    exists_edge_correction_of_innerFibration ((pre i).app C)
      (innerFibration_pre_app_of_mono i C) uB
      ((uX.map ((pre f).app C)).ofEq (hv y₁) (hv y₂)) hw
  have hedge : (uB'.map ((pre i).app C)).edge =
      (uX.map ((pre f).app C)).edge := huB'2
  have hagree : yonedaEquiv.symm uB'.edge ≫ (pre i).app C =
      yonedaEquiv.symm uX.edge ≫ (pre f).app C := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simp only [Equiv.apply_symm_apply]
    rw [← Edge.map_edge, ← Edge.map_edge]
    exact hedge
  obtain ⟨Wmap, hW1, hW2⟩ := exists_pre_lift_of_isPushout sq C _ _ hagree
  have hδ : ∀ (eBedge : ((ihom B).obj C) _⦋1⦌) (eXedge : ((ihom X).obj C) _⦋1⦌)
      (hB : Wmap ≫ (pre f').app C = yonedaEquiv.symm eBedge)
      (hX : Wmap ≫ (pre j).app C = yonedaEquiv.symm eXedge)
      (y : ((ihom Y).obj C) _⦋0⦌) (idx : Fin 2)
      (hBy : ((ihom B).obj C).δ idx eBedge = ((pre f').app C).app _ y)
      (hXy : ((ihom X).obj C).δ idx eXedge = ((pre j).app C).app _ y),
      ((ihom Y).obj C).δ idx (yonedaEquiv Wmap) = y := by
    intro eBedge eXedge hB hX y idx hBy hXy
    have hks : yonedaEquiv.symm (((ihom Y).obj C).δ idx (yonedaEquiv Wmap)) =
        yonedaEquiv.symm y := by
      apply (isPullback_pre_app_of_isPushout sq C).hom_ext
      · apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp]
        simp only [Equiv.apply_symm_apply]
        calc ((pre f').app C).app _ (((ihom Y).obj C).δ idx (yonedaEquiv Wmap))
            = ((ihom B).obj C).δ idx (((pre f').app C).app _ (yonedaEquiv Wmap)) :=
              δ_naturality_apply _ _ _
          _ = ((ihom B).obj C).δ idx eBedge := by
              rw [← yonedaEquiv_comp, hB, Equiv.apply_symm_apply]
          _ = ((pre f').app C).app _ y := hBy
      · apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp]
        simp only [Equiv.apply_symm_apply]
        calc ((pre j).app C).app _ (((ihom Y).obj C).δ idx (yonedaEquiv Wmap))
            = ((ihom X).obj C).δ idx (((pre j).app C).app _ (yonedaEquiv Wmap)) :=
              δ_naturality_apply _ _ _
          _ = ((ihom X).obj C).δ idx eXedge := by
              rw [← yonedaEquiv_comp, hX, Equiv.apply_symm_apply]
          _ = ((pre j).app C).app _ y := hXy
    have h2 := congrArg yonedaEquiv hks
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
  have hsrc : ((ihom Y).obj C).δ 1 (yonedaEquiv Wmap) = y₁ :=
    hδ uB'.edge uX.edge hW1 hW2 y₁ 1 uB'.src_eq uX.src_eq
  have htgt : ((ihom Y).obj C).δ 0 (yonedaEquiv Wmap) = y₂ :=
    hδ uB'.edge uX.edge hW1 hW2 y₂ 0 uB'.tgt_eq uX.tgt_eq
  let eY : Edge y₁ y₂ := Edge.mk (yonedaEquiv Wmap) hsrc htgt
  refine ⟨eY.toHoHom, ?_⟩
  have hedgeY : (eY.map ((pre f').app C)).edge = uB'.edge := by
    change ((pre f').app C).app _ (yonedaEquiv Wmap) = uB'.edge
    rw [← yonedaEquiv_comp, hW1, Equiv.apply_symm_apply]
  rw [← Edge.toHoHom_map, show eY.map ((pre f').app C) = uB' from
    Edge.ext hedgeY, huB'1]
  exact huB

/-! ## Conditional assemblies (§4 of the header) -/

/-- Precomposition with a monomorphism into a quasicategory satisfies
`innerIsoFibrations` as soon as the prism strict extension property
the additional comparison obligation holds for that pair: the inner fibration half
is `SSet.innerFibration_pre_app_of_mono` and the isofibration half
is `SSet.hoFunctor_pre_isIsofibration_of_prismStrictExtension`
(the supporting results). -/
theorem innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension
    [Mono i] (C : SSet.{u}) [Quasicategory C]
    (h : HoPrePrismStrictExtension i C) :
    innerIsoFibrations ((pre i).app C) := by
  rw [innerIsoFibrations.mem_iff]
  exact ⟨(innerFibration_iff _).1 (innerFibration_pre_app_of_mono i C),
    hoFunctor_pre_isIsofibration_of_prismStrictExtension C h⟩

/-- Essential surjectivity plus fullness of precomposition with a
cobase change, granted the isofibration property (A) of the left
leg at the given target: essential surjectivity is the supporting results
(`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`) and
fullness is `SSet.hoFunctor_pre_full_of_isPushout` here, which
needs no isofibration input. -/
theorem hoFunctor_pre_essSurj_full_of_isPushout_of_isIsofibration
    (sq : IsPushout i f f' j) [Mono i] (hf : categoricalEquivalences f)
    (C : SSet.{u}) [Quasicategory C]
    (hIso : (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration) :
    (hoFunctor.map ((pre f').app C)).toFunctor.EssSurj ∧
      (hoFunctor.map ((pre f').app C)).toFunctor.Full :=
  ⟨hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration sq hf C hIso,
    hoFunctor_pre_full_of_isPushout sq hf C⟩

/-- **Cobase change of a categorical equivalence along a
monomorphism, granted (A) and faithfulness.** This is the the supporting result
assembly
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful`
with the fullness input supplied unconditionally by
`SSet.hoFunctor_pre_full_of_isPushout` here. The remaining
hypotheses are exactly the additional comparison obligation (the isofibration property of
the left leg for every quasicategory target, i.e. by §0 the prism
strict extension property of §2) and the additional comparison obligation (faithfulness,
i.e. correction of `2`-simplices rel boundary, §3). -/
theorem categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful
    (sq : IsPushout i f f' j) [Mono i] (hf : categoricalEquivalences f)
    (hIso : ∀ (C : SSet.{u}) [Quasicategory C],
      (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration)
    (hFaith : ∀ (C : SSet.{u}) [Quasicategory C],
      (hoFunctor.map ((pre f').app C)).toFunctor.Faithful) :
    categoricalEquivalences f' :=
  categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful
    sq hf hIso
    (fun C _ => ⟨hoFunctor_pre_full_of_isPushout sq hf C, hFaith C⟩)

/-! ## The `0`-dimensional cell of (A) (§2 of the header) -/

/-- No simplex of `∂Δ[0]` exists in any degree: `∂Δ[0]` is the
bottom subcomplex (`SSet.boundary_zero`). -/
private lemma cobaseGen_boundaryZero_obj_elim {Δ : SimplexCategoryᵒᵖ}
    (x : (∂Δ[0] : SSet.{u}).obj Δ) : False := by
  have h := x.2
  simp only [boundary_zero, Subfunctor.bot_obj, Set.mem_empty_iff_false] at h

/-- Maps out of `∂Δ[0] ⊗ W` are unique, since `∂Δ[0]` has no
simplices. -/
private lemma cobaseGen_eq_of_boundaryZero_tensor {W C : SSet.{u}}
    (F G : (∂Δ[0] : SSet.{u}) ⊗ W ⟶ C) : F = G := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro x
  exact (cobaseGen_boundaryZero_obj_elim x.1).elim

/-- Vertices of `Fun(∂Δ[0], C)` are unique, through the prism
dictionary `SSet.ihomSimplexEquiv` at `n = 0`. -/
private lemma cobaseGen_subsingleton_ihom_vertex_boundaryZero (C : SSet.{u})
    (s t : ((ihom (∂Δ[0] : SSet.{u})).obj C) _⦋0⦌) : s = t := by
  apply (ihomSimplexEquiv (∂Δ[0] : SSet.{u}) C 0).symm.injective
  exact cobaseGen_eq_of_boundaryZero_tensor _ _

/-- **The `0`-dimensional cell of the additional comparison obligation.** The prism strict
extension property holds along `∂Δ[0].ι` for every target `C`
(no quasicategory hypothesis is needed in dimension `0`): the
prism over `∂Δ[0]` is unique
(`cobaseGen_eq_of_boundaryZero_tensor`), vertices of
`Fun(∂Δ[0], C)` are unique, and the degenerate prism of the
identity edge at the prescribed vertex is the required extension.
This is the `n = 0` case of the cell step of §2 of the header; the
cases `n ≥ 1` need the prism triangulation recorded there as
the additional comparison obligation(1). -/
theorem hoPrePrismStrictExtension_boundary_zero (C : SSet.{u}) :
    HoPrePrismStrictExtension ∂Δ[0].ι C := by
  intro b a' e _he
  have h0 : ((ihom (Δ[0] : SSet.{u})).obj C).δ 1
      (ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id b).edge)) = b := by
    rw [ihomSimplexOfPrism_ihomPrismOfSimplex]
    exact (Edge.id b).src_eq
  have h1 : ((ihom (Δ[0] : SSet.{u})).obj C).δ 0
      (ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id b).edge)) = b := by
    rw [ihomSimplexOfPrism_ihomPrismOfSimplex]
    exact (Edge.id b).tgt_eq
  have hEq : edgeOfPrism (ihomPrismOfSimplex (Edge.id b).edge) h0 h1 =
      Edge.id b :=
    Edge.ext (by rw [edgeOfPrism_edge, ihomSimplexOfPrism_ihomPrismOfSimplex])
  exact ⟨ihomPrismOfSimplex (Edge.id b).edge, b,
    cobaseGen_subsingleton_ihom_vertex_boundaryZero C _ _, h0, h1,
    hEq.symm ▸ Edge.isEquivalence_id b,
    cobaseGen_eq_of_boundaryZero_tensor _ _⟩

/-- **the additional comparison obligation for the boundary inclusion `∂Δ[0].ι`.** For every
quasicategory `C`, precomposition with `∂Δ[0].ι` induces an
isofibration on homotopy categories of functor objects into `C`,
by `SSet.hoPrePrismStrictExtension_boundary_zero` and the prism
reduction of the supporting results. For `∂Δ[n].ι` with `n ≥ 1` and a general
quasicategory target this remains the additional comparison obligation; for Kan complex
targets and every `n` it is the supporting results
(`SSet.hoFunctor_pre_isIsofibration_boundary_kanComplex`). -/
theorem hoFunctor_pre_isIsofibration_boundary_zero (C : SSet.{u})
    [Quasicategory C] :
    (hoFunctor.map ((pre ∂Δ[0].ι).app C)).toFunctor.IsIsofibration :=
  hoFunctor_pre_isIsofibration_of_prismStrictExtension C
    (hoPrePrismStrictExtension_boundary_zero C)

/-- Precomposition with `∂Δ[0].ι` into a quasicategory satisfies
`innerIsoFibrations`, as follows from
`SSet.hoPrePrismStrictExtension_boundary_zero` read through
`SSet.innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension`. -/
theorem innerIsoFibrations_pre_app_boundary_zero (C : SSet.{u})
    [Quasicategory C] :
    innerIsoFibrations ((pre ∂Δ[0].ι).app C) :=
  innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension C
    (hoPrePrismStrictExtension_boundary_zero C)

end SSet

end
