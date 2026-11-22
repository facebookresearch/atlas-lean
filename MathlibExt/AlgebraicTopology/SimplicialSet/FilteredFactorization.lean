/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Filtered-colimit factorization and functor objects for simplicial sets

Neutral (model-structure-free) infrastructure split out of the
filtered-colimit closure module for categorical equivalences: nothing
here mentions any weak-equivalence or anodyne class.

* Simplex-wise factorization through filtered colimits: for a same-universe
  filtered colimit cocone `c` in `SSet.{u}`, simplices, edges and
  `2`-simplices of `c.pt` come from a single stage, with faces mapping to
  the prescribed faces
  (`SSet.exists_simplex_factorization_of_isFilteredColimit`,
  `SSet.exists_edge_factorization_of_isFilteredColimit`,
  `SSet.exists_compStruct_factorization_of_isFilteredColimit`), by finite
  presentability (`IsFinitelyPresentable.exists_hom_of_isColimit`, with the
  instance from `Mathlib.AlgebraicTopology.SimplicialSet.Presentable`);
  and simplices at two stages with equal colimit images already agree
  at a common later stage (`SSet.exists_simplex_eq_at_stage`, from
  `IsFinitelyPresentable.exists_eq_of_isColimit`).

* The functor-object limit: for *any* colimit cocone `c` (no filtered
  hypothesis is needed) and any `C`, the cone `SSet.ihomCone` with apex
  `(ihom c.pt).obj C` and legs `(pre (c.ι.app j)).app C` is a limit cone
  over `SSet.ihomDiagram` (`SSet.isLimit_ihomCone`), and precomposition
  with a colimit map is the induced map of these limit cones
  (`SSet.pre_app_comp_ihomCone_π_app`).

## References

* P. Goerss and J. Jardine, *Simplicial Homotopy Theory*, VII Lemma 3.5
  (finite simplicial sets factor through filtered colimits).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-- Precomposition with an identity map, at the level of functor objects:
`(pre (𝟙 X)).app C` is the identity of `Fun(X, C)`. -/
private lemma pre_id_app (X C : SSet.{u}) :
    (pre (𝟙 X)).app C = 𝟙 ((ihom X).obj C) := by
  rw [pre_id]; rfl

/-- Precomposition is contravariantly functorial at the level of functor
objects: `(pre (f ≫ g)).app C` is `(pre g).app C ≫ (pre f).app C`. -/
private lemma pre_comp_app {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : SSet.{u}) :
    (pre (f ≫ g)).app C = (pre g).app C ≫ (pre f).app C := by
  rw [pre_map]; rfl

section FilteredFactorization

variable {J : Type u} [Category.{u} J] [IsFiltered J] {F : J ⥤ SSet.{u}}
  {c : Cocone F} (hc : IsColimit c)

include hc

/-- Every simplex of a filtered colimit of simplicial sets comes from a
simplex at some stage: the `Δ[n]`-probe form of
`IsFinitelyPresentable.exists_hom_of_isColimit`, transported along
`SSet.yonedaEquiv`. -/
theorem exists_simplex_factorization_of_isFilteredColimit {n : ℕ}
    (σ : c.pt _⦋n⦌) :
    ∃ (j : J) (σ' : F.obj j _⦋n⦌), (c.ι.app j).app (op ⦋n⦌) σ' = σ := by
  obtain ⟨j, φ, hφ⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc
    (yonedaEquiv.symm σ)
  refine ⟨j, yonedaEquiv φ, ?_⟩
  calc (c.ι.app j).app (op ⦋n⦌) (yonedaEquiv φ)
      = yonedaEquiv (yonedaEquiv.symm
          ((c.ι.app j).app (op ⦋n⦌) (yonedaEquiv φ))) :=
        (Equiv.apply_symm_apply _ _).symm
    _ = yonedaEquiv (φ ≫ c.ι.app j) := by
        rw [← yonedaEquiv_symm_comp, Equiv.symm_apply_apply]
    _ = yonedaEquiv (yonedaEquiv.symm σ) := by rw [hφ]
    _ = σ := Equiv.apply_symm_apply _ _

/-- Every edge of a filtered colimit comes from an edge at some stage,
with endpoints mapping to the given endpoints: the `Δ[1]`-probe form of
factorization, in the edge dictionary of
`MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration`. -/
theorem exists_edge_factorization_of_isFilteredColimit {x y : c.pt _⦋0⦌}
    (e : Edge x y) :
    ∃ (j : J) (x' y' : F.obj j _⦋0⦌) (e' : Edge x' y'),
      (c.ι.app j).app (op ⦋0⦌) x' = x ∧ (c.ι.app j).app (op ⦋0⦌) y' = y ∧
        (c.ι.app j).app (op ⦋1⦌) e'.edge = e.edge := by
  obtain ⟨j, σ', hσ'⟩ := exists_simplex_factorization_of_isFilteredColimit hc e.edge
  refine ⟨j, (F.obj j).δ 1 σ', (F.obj j).δ 0 σ', Edge.mk σ' rfl rfl, ?_, ?_, hσ'⟩
  · rw [δ_naturality_apply, hσ']; exact e.src_eq
  · rw [δ_naturality_apply, hσ']; exact e.tgt_eq

/-- Every `2`-simplex of a filtered colimit comes from a `2`-simplex at
some stage, with faces mapping to the faces of the given simplex. For a
`Edge.CompStruct` in the colimit this gives, at a single stage, a
`2`-simplex over it whose three faces lie over the three given edges:
the `Δ[2]`-probe form of factorization. -/
theorem exists_compStruct_factorization_of_isFilteredColimit
    {x₀ x₁ x₂ : c.pt _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    ∃ (j : J) (σ' : F.obj j _⦋2⦌),
      (c.ι.app j).app (op ⦋2⦌) σ' = h.simplex ∧
        (c.ι.app j).app (op ⦋1⦌) ((F.obj j).δ 2 σ') = e₀₁.edge ∧
          (c.ι.app j).app (op ⦋1⦌) ((F.obj j).δ 0 σ') = e₁₂.edge ∧
            (c.ι.app j).app (op ⦋1⦌) ((F.obj j).δ 1 σ') = e₀₂.edge := by
  obtain ⟨j, σ', hσ'⟩ := exists_simplex_factorization_of_isFilteredColimit hc h.simplex
  refine ⟨j, σ', hσ', ?_, ?_, ?_⟩
  · rw [δ_naturality_apply, hσ']; exact h.d₂
  · rw [δ_naturality_apply, hσ']; exact h.d₀
  · rw [δ_naturality_apply, hσ']; exact h.d₁

/-- Two simplices at stages of a filtered diagram with the same image
in the colimit already agree at a common later stage. This is the
simplex form of `IsFinitelyPresentable.exists_eq_of_isColimit` at
`Δ[n]`, transported along `SSet.yonedaEquiv`. -/
theorem exists_simplex_eq_at_stage {n : ℕ} {i j : J}
    {a : F.obj i _⦋n⦌} {b : F.obj j _⦋n⦌}
    (h : (c.ι.app i).app (op ⦋n⦌) a = (c.ι.app j).app (op ⦋n⦌) b) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k),
      (F.map u).app (op ⦋n⦌) a = (F.map v).app (op ⦋n⦌) b := by
  have h' : yonedaEquiv.symm a ≫ c.ι.app i =
      yonedaEquiv.symm b ≫ c.ι.app j := by
    rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, h]
  obtain ⟨k, u, v, huv⟩ :=
    IsFinitelyPresentable.exists_eq_of_isColimit
      (X := (Δ[n] : SSet.{u})) hc
      (yonedaEquiv.symm a) (yonedaEquiv.symm b) h'
  refine ⟨k, u, v, ?_⟩
  have key := congrArg yonedaEquiv huv
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using key

end FilteredFactorization

section IhomLimit

variable {J : Type u} [Category.{u} J] (F : J ⥤ SSet.{u}) (C : SSet.{u})

/-- The diagram of simplicial functor objects associated to a diagram
`F : J ⥤ SSet` and a fixed target `C`: at `j` it is `Fun(F.obj j, C)`,
and the transition maps are precomposition with the maps of `F`. A
(colimit) cocone on `F` induces a cone on this diagram, see
`SSet.ihomCone`. -/
def ihomDiagram : Jᵒᵖ ⥤ SSet.{u} where
  obj j := (ihom (F.obj j.unop)).obj C
  map u := (pre (F.map u.unop)).app C
  map_id j := by
    change (pre (F.map (𝟙 j).unop)).app C = 𝟙 _
    rw [show (𝟙 j).unop = 𝟙 j.unop from rfl, F.map_id]
    exact pre_id_app _ _
  map_comp u v := by
    change (pre (F.map (u ≫ v).unop)).app C =
      (pre (F.map u.unop)).app C ≫ (pre (F.map v.unop)).app C
    rw [show (u ≫ v).unop = v.unop ≫ u.unop from rfl, F.map_comp]
    exact pre_comp_app _ _ _

@[simp]
lemma ihomDiagram_obj (j : Jᵒᵖ) :
    (ihomDiagram F C).obj j = (ihom (F.obj j.unop)).obj C := rfl

@[simp]
lemma ihomDiagram_map {j k : Jᵒᵖ} (u : j ⟶ k) :
    (ihomDiagram F C).map u = (pre (F.map u.unop)).app C := rfl

/-- The cone on the functor-object diagram `SSet.ihomDiagram F C`
induced by a cocone `c` on `F`: the apex is `Fun(c.pt, C)` and the legs
are precomposition with the cocone legs. When `c` is a colimit cocone
this is a limit cone, see `SSet.isLimit_ihomCone`. -/
def ihomCone (c : Cocone F) : Cone (ihomDiagram F C) where
  pt := (ihom c.pt).obj C
  π :=
    { app := fun j => (pre (c.ι.app j.unop)).app C
      naturality := by
        intro j k u
        change (𝟙 ((ihom c.pt).obj C)) ≫ (pre (c.ι.app k.unop)).app C =
          (pre (c.ι.app j.unop)).app C ≫ (pre (F.map u.unop)).app C
        rw [Category.id_comp, ← pre_comp_app, c.w] }

@[simp]
lemma ihomCone_π_app (c : Cocone F) (j : Jᵒᵖ) :
    (ihomCone F C c).π.app j = (pre (c.ι.app j.unop)).app C := rfl

/-- Precomposition with a map of cocone apexes is the induced map of the
functor-object limit cones: it commutes with the cone legs via the
stage maps. This is the exact compatibility consumed by the `hFun`
test for a colimit map. -/
theorem pre_app_comp_ihomCone_π_app {G : J ⥤ SSet.{u}} {cF : Cocone F}
    {cG : Cocone G} (α : F ⟶ G) (φ : cF.pt ⟶ cG.pt)
    (hφ : ∀ j, cF.ι.app j ≫ φ = α.app j ≫ cG.ι.app j) (j : J) :
    (pre φ).app C ≫ (ihomCone F C cF).π.app (op j) =
      (ihomCone G C cG).π.app (op j) ≫ (pre (α.app j)).app C := by
  have e1 : (pre φ).app C ≫ (pre (cF.ι.app j)).app C =
      (pre (cF.ι.app j ≫ φ)).app C := (pre_comp_app (cF.ι.app j) φ C).symm
  have e2 : (pre (cG.ι.app j)).app C ≫ (pre (α.app j)).app C =
      (pre (α.app j ≫ cG.ι.app j)).app C :=
    (pre_comp_app (α.app j) (cG.ι.app j) C).symm
  change (pre φ).app C ≫ (pre (cF.ι.app j)).app C =
    (pre (cG.ι.app j)).app C ≫ (pre (α.app j)).app C
  exact e1.trans ((congrArg (fun t => (pre t).app C) (hφ j)).trans e2.symm)

/-- Simplices of a simplicial functor object are tensor maps out of the
first variable: `s`-simplices of `(ihom X).obj K` correspond, by Yoneda
and currying, to maps `X ⊗ Δ[s] ⟶ K`. For `s = ⦋n⦌` this is the
symmetric of the landed prism dictionary `SSet.ihomSimplexEquiv X K n`
of `IhomPrism.lean`; it is stated here for an arbitrary
simplex-category object `s`, as required by evaluation at `op s` in
`SSet.isLimit_ihomCone`, without importing the endpoint-inclusion
module into this lower-level filtered-colimit interface. -/
noncomputable def ihomTensorSimplexEquiv (s : SimplexCategory) (X K : SSet.{u}) :
    ((ihom X).obj K).obj (op s) ≃ (X ⊗ stdSimplex.obj s ⟶ K) :=
  yonedaEquiv.symm.trans ((ihom.adjunction X).homEquiv (stdSimplex.obj s) K).symm

/-- Naturality of `ihomTensorSimplexEquiv` in the first variable:
precomposition on simplices of functor objects is precomposition with
`f ▷ Δ[s]` on tensor maps, by `MonoidalClosed.uncurry_pre_app`. -/
lemma ihomTensorSimplexEquiv_pre_app (s : SimplexCategory) {X Y K : SSet.{u}}
    (f : X ⟶ Y) (x : ((ihom Y).obj K).obj (op s)) :
    ihomTensorSimplexEquiv s X K (((pre f).app K).app (op s) x) =
      (f ▷ stdSimplex.obj s) ≫ ihomTensorSimplexEquiv s Y K x := by
  have h1 : yonedaEquiv.symm (((pre f).app K).app (op s) x) =
      yonedaEquiv.symm x ≫ (pre f).app K := by
    rw [yonedaEquiv_symm_comp]
  simp only [ihomTensorSimplexEquiv, Equiv.trans_apply, h1]
  change MonoidalClosed.uncurry (yonedaEquiv.symm x ≫ (pre f).app K) =
    (f ▷ stdSimplex.obj s) ≫ MonoidalClosed.uncurry (yonedaEquiv.symm x)
  rw [MonoidalClosed.uncurry_pre_app]

/-- Evaluation at `[s]` identifies the functor-object diagram with the
diagram of tensor hom-sets into `C`: the components are
`ihomTensorSimplexEquiv`. -/
noncomputable def ihomEvaluationNatIso (s : SimplexCategory) :
    (ihomDiagram F C ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op s)) ≅
      ((F ⋙ tensorRight (stdSimplex.obj s)).op ⋙ yoneda.obj C) :=
  NatIso.ofComponents (fun j => Equiv.toIso (ihomTensorSimplexEquiv s (F.obj j.unop) C))
    (by
      intro j₁ j₂ u
      apply ConcreteCategory.hom_ext
      intro x
      change ihomTensorSimplexEquiv s (F.obj j₂.unop) C
          (((pre (F.map u.unop)).app C).app (op s) x) =
        (F.map u.unop ▷ stdSimplex.obj s) ≫
          ihomTensorSimplexEquiv s (F.obj j₁.unop) C x
      exact ihomTensorSimplexEquiv_pre_app s (F.map u.unop) x)

/-- **Functor objects turn colimits into limits.** For every colimit
cocone `c` in `SSet.{u}` (of any shape) and every `C`, the induced cone
`SSet.ihomCone` on the functor-object diagram is a limit cone: the
simplicial functor object out of a colimit is the limit of the functor
objects out of the stages. The proof evaluates at every `[s]`, where
both sides become tensor hom-sets, and uses that `(- ⊗ Δ[s])` preserves
colimits and that `yoneda.obj C` sends the resulting colimit cocone to
a limit cone. -/
noncomputable def isLimit_ihomCone {c : Cocone F} (hc : IsColimit c) :
    IsLimit (ihomCone F C c) := by
  apply evaluationJointlyReflectsLimits
  rintro ⟨s⟩
  have hκ2 : IsLimit ((yoneda.obj C).mapCone
      (((tensorRight (stdSimplex.obj s)).mapCocone c).op)) :=
    isLimitOfPreserves (yoneda.obj C)
      (isColimitOfPreserves (tensorRight (stdSimplex.obj s)) hc).op
  have h2 : IsLimit ((Cone.postcomposeEquivalence
      (ihomEvaluationNatIso F C s)).inverse.obj
        ((yoneda.obj C).mapCone
          (((tensorRight (stdSimplex.obj s)).mapCocone c).op))) :=
    IsLimit.ofPreservesConeTerminal
      (Cone.postcomposeEquivalence (ihomEvaluationNatIso F C s)).inverse hκ2
  refine IsLimit.ofIsoLimit h2 (Cone.ext
    (Equiv.toIso (ihomTensorSimplexEquiv s c.pt C)).symm ?_)
  intro j
  apply ConcreteCategory.hom_ext
  intro g
  change (ihomTensorSimplexEquiv s (F.obj j.unop) C).symm
      ((c.ι.app j.unop ▷ stdSimplex.obj s) ≫ g) =
    ((pre (c.ι.app j.unop)).app C).app (op s)
      ((ihomTensorSimplexEquiv s c.pt C).symm g)
  rw [Equiv.symm_apply_eq, ihomTensorSimplexEquiv_pre_app]
  congr 1
  exact (Equiv.apply_symm_apply _ _).symm

end IhomLimit

end SSet
