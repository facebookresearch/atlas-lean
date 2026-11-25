/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-! # The prism dictionary for internal homs of simplicial sets

Simplices of `(ihom X).obj C` in degree `n` are prisms
`X ⊗ Δ[n] ⟶ C`, by currying and Yoneda (`SSet.ihomSimplexOfPrism`,
`SSet.ihomPrismOfSimplex`, packaged as `SSet.ihomSimplexEquiv`).
Faces, degeneracies, and precomposition in the source variable are
precomposition of prisms, and vertices in degree `0` recover
`SSet.ihomVertexEquiv` through the sections
`SSet.prismSectionZero` and `SSet.prismSectionAt`.

This module is generic simplicial-set infrastructure: it has no
dependence on `SSet.coherentIso` or on the Joyal model structure.
Its consumer in the Joyal programme is
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint`,
where prisms over `coherentIso` are used for the pattern-map
contraction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {X B C : SSet.{u}}

/-! ## The prism dictionary

Simplices of `(ihom X).obj C` in degree `n` are prisms `X ⊗ Δ[n] ⟶ C`,
by currying and Yoneda. Faces and degeneracies are precomposition with
`X ◁ stdSimplex.δ i` resp. `X ◁ stdSimplex.σ i`, precomposition in the
`X` variable is whiskering on the right, and vertices recover
`SSet.ihomVertexEquiv` at the two endpoints of `Δ[1]`. -/

/-- The `n`-simplex of `(ihom X).obj C` corresponding to a prism
`F : X ⊗ Δ[n] ⟶ C`, defined as `yonedaEquiv (curry F)`. -/
noncomputable def ihomSimplexOfPrism {n : ℕ} (F : X ⊗ Δ[n] ⟶ C) :
    ((ihom X).obj C) _⦋n⦌ :=
  yonedaEquiv (MonoidalClosed.curry F)

/-- The prism `X ⊗ Δ[n] ⟶ C` corresponding to an `n`-simplex of
`(ihom X).obj C`, defined as `uncurry (yonedaEquiv.symm s)`. -/
noncomputable def ihomPrismOfSimplex {n : ℕ} (s : ((ihom X).obj C) _⦋n⦌) :
    X ⊗ Δ[n] ⟶ C :=
  MonoidalClosed.uncurry (yonedaEquiv.symm s)

@[simp]
lemma ihomPrismOfSimplex_ihomSimplexOfPrism {n : ℕ} (F : X ⊗ Δ[n] ⟶ C) :
    ihomPrismOfSimplex (ihomSimplexOfPrism F) = F := by
  simp [ihomPrismOfSimplex, ihomSimplexOfPrism]

@[simp]
lemma ihomSimplexOfPrism_ihomPrismOfSimplex {n : ℕ}
    (s : ((ihom X).obj C) _⦋n⦌) :
    ihomSimplexOfPrism (ihomPrismOfSimplex s) = s := by
  simp [ihomPrismOfSimplex, ihomSimplexOfPrism]

/-- The prism dictionary as an equivalence: prisms `X ⊗ Δ[n] ⟶ C` are
exactly the `n`-simplices of `(ihom X).obj C`. -/
noncomputable def ihomSimplexEquiv (X C : SSet.{u}) (n : ℕ) :
    (X ⊗ Δ[n] ⟶ C) ≃ ((ihom X).obj C) _⦋n⦌ where
  toFun := ihomSimplexOfPrism
  invFun := ihomPrismOfSimplex
  left_inv := ihomPrismOfSimplex_ihomSimplexOfPrism
  right_inv := ihomSimplexOfPrism_ihomPrismOfSimplex

/-- Faces of a prism simplex are the simplices of the face prisms,
obtained by precomposing with `X ◁ stdSimplex.δ i`. -/
lemma δ_ihomSimplexOfPrism {n : ℕ} (F : X ⊗ Δ[n + 1] ⟶ C)
    (i : Fin (n + 2)) :
    ((ihom X).obj C).δ i (ihomSimplexOfPrism F) =
      ihomSimplexOfPrism ((X ◁ stdSimplex.δ i) ≫ F) := by
  have h : ((ihom X).obj C).δ i (ihomSimplexOfPrism F) =
      yonedaEquiv (stdSimplex.δ i ≫ MonoidalClosed.curry F) :=
    (stdSimplex.yonedaEquiv_δ_comp _ i).symm
  rw [h, ← MonoidalClosed.curry_natural_left]
  rfl

/-- Degeneracies of a prism simplex are the simplices of the degenerate
prisms, obtained by precomposing with `X ◁ stdSimplex.σ i`. -/
lemma σ_ihomSimplexOfPrism {n : ℕ} (F : X ⊗ Δ[n] ⟶ C) (i : Fin (n + 1)) :
    ((ihom X).obj C).σ i (ihomSimplexOfPrism F) =
      ihomSimplexOfPrism ((X ◁ stdSimplex.σ i) ≫ F) := by
  have h : ((ihom X).obj C).σ i (ihomSimplexOfPrism F) =
      yonedaEquiv (stdSimplex.σ i ≫ MonoidalClosed.curry F) :=
    (stdSimplex.yonedaEquiv_σ_comp _ i).symm
  rw [h, ← MonoidalClosed.curry_natural_left]
  rfl

/-- Precomposition in the source variable: the image of a prism simplex
under `(pre f).app C` is the simplex of the prism precomposed with
`f ▷ Δ[n]`. -/
lemma ihomSimplexOfPrism_pre_app {n : ℕ} (f : B ⟶ X) (F : X ⊗ Δ[n] ⟶ C) :
    ((pre f).app C).app (op ⦋n⦌) (ihomSimplexOfPrism F) =
      ihomSimplexOfPrism ((f ▷ Δ[n]) ≫ F) := by
  have h : ((pre f).app C).app (op ⦋n⦌) (ihomSimplexOfPrism F) =
      yonedaEquiv (MonoidalClosed.curry F ≫ (pre f).app C) :=
    (yonedaEquiv_comp _ _).symm
  rw [h, MonoidalClosed.curry_pre_app]
  rfl

/-- The section `X ⟶ X ⊗ Δ[0]` of the first projection, used to read
the endpoint maps of a prism: it is `(ρ_ X).inv` followed by
`X ◁ Δ0IsoUnit.inv`. -/
noncomputable def prismSectionZero (X : SSet.{u}) : X ⟶ X ⊗ Δ[0] :=
  (ρ_ X).inv ≫ (X ◁ Δ0IsoUnit.inv)

/-- In degree `0` the prism dictionary recovers the vertex dictionary:
the simplex of a prism `F : X ⊗ Δ[0] ⟶ C` is the vertex classified by
`prismSectionZero X ≫ F`. -/
lemma ihomSimplexOfPrism_zero (F : X ⊗ Δ[0] ⟶ C) :
    ihomSimplexOfPrism F =
      ihomVertexEquiv X C (prismSectionZero X ≫ F) := by
  have h1 : ihomSimplexOfPrism F =
      unitHomEquiv _ (Δ0IsoUnit.inv ≫ MonoidalClosed.curry F) :=
    yonedaEquiv_eq_unitHomEquiv _ _
  have h2 : Δ0IsoUnit.inv ≫ MonoidalClosed.curry F =
      MonoidalClosed.curry ((X ◁ Δ0IsoUnit.inv) ≫ F) :=
    (MonoidalClosed.curry_natural_left _ _).symm
  have h3 : MonoidalClosed.curry' (prismSectionZero X ≫ F) =
      MonoidalClosed.curry ((X ◁ Δ0IsoUnit.inv) ≫ F) := by
    rw [MonoidalClosed.curry', prismSectionZero, ← Category.assoc,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h1, h2, ← h3, ihomVertexEquiv_eq]

/-- The source endpoint of a `Δ[1]`-prism simplex is the vertex
classified by the restriction of the prism along `X ◁ stdSimplex.δ 1`
followed by the section. -/
lemma δ_one_ihomSimplexOfPrism (F : X ⊗ Δ[1] ⟶ C) :
    ((ihom X).obj C).δ 1 (ihomSimplexOfPrism F) =
      ihomVertexEquiv X C
        (prismSectionZero X ≫ (X ◁ stdSimplex.δ 1) ≫ F) := by
  rw [δ_ihomSimplexOfPrism, ihomSimplexOfPrism_zero]

/-- The target endpoint of a `Δ[1]`-prism simplex is the vertex
classified by the restriction of the prism along `X ◁ stdSimplex.δ 0`
followed by the section. -/
lemma δ_zero_ihomSimplexOfPrism (F : X ⊗ Δ[1] ⟶ C) :
    ((ihom X).obj C).δ 0 (ihomSimplexOfPrism F) =
      ihomVertexEquiv X C
        (prismSectionZero X ≫ (X ◁ stdSimplex.δ 0) ≫ F) := by
  rw [δ_ihomSimplexOfPrism, ihomSimplexOfPrism_zero]

/-- The edge of `(ihom X).obj C` determined by a prism `F : X ⊗ Δ[1] ⟶ C`
between prescribed vertices, given proofs that its endpoints are those
vertices. -/
noncomputable def edgeOfPrism (F : X ⊗ Δ[1] ⟶ C)
    {x₀ x₁ : ((ihom X).obj C) _⦋0⦌}
    (h₀ : ((ihom X).obj C).δ 1 (ihomSimplexOfPrism F) = x₀)
    (h₁ : ((ihom X).obj C).δ 0 (ihomSimplexOfPrism F) = x₁) :
    Edge x₀ x₁ :=
  Edge.mk (ihomSimplexOfPrism F) h₀ h₁

@[simp]
lemma edgeOfPrism_edge (F : X ⊗ Δ[1] ⟶ C)
    {x₀ x₁ : ((ihom X).obj C) _⦋0⦌}
    (h₀ : ((ihom X).obj C).δ 1 (ihomSimplexOfPrism F) = x₀)
    (h₁ : ((ihom X).obj C).δ 0 (ihomSimplexOfPrism F) = x₁) :
    (edgeOfPrism F h₀ h₁).edge = ihomSimplexOfPrism F :=
  rfl

/-- The section `X ⟶ X ⊗ Δ[m]` at the vertex `κ` of `Δ[m]`. -/
noncomputable def prismSectionAt (X : SSet.{u}) {m : ℕ} (κ : Fin (m + 1)) :
    X ⟶ X ⊗ Δ[m] :=
  (ρ_ X).inv ≫
    (X ◁ (Δ0IsoUnit.inv ≫
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ κ)))

@[simp]
lemma prismSectionAt_app_fst (X : SSet.{u}) {m : ℕ} (κ : Fin (m + 1))
    {Δ : SimplexCategoryᵒᵖ} (s : X.obj Δ) :
    ((prismSectionAt X κ).app Δ s).1 = s :=
  rfl

@[simp]
lemma asOrderHom_prismSectionAt_app_snd (X : SSet.{u}) {m : ℕ}
    (κ : Fin (m + 1)) {Δ : SimplexCategoryᵒᵖ} (s : X.obj Δ)
    (k : Fin (Δ.unop.len + 1)) :
    (stdSimplex.asOrderHom ((prismSectionAt X κ).app Δ s).2) k = κ := by
  simp only [prismSectionAt, NatTrans.comp_app, types_comp_apply]
  rfl

/-- The section at vertex `0` is `prismSectionZero`: the two names
denote the same section, `prismSectionZero` being the `m = 0` case
used for endpoint restrictions of prisms. -/
lemma prismSectionAt_zero (X : SSet.{u}) :
    prismSectionAt X (0 : Fin 1) = prismSectionZero X := by
  simp [prismSectionZero, prismSectionAt]

/-- Restricting a prism along `X ◁ stdSimplex.δ 1` and then reading the
endpoint is precomposition with the section at vertex `0`. -/
lemma prismSectionZero_whiskerLeft_δ_one (X : SSet.{u}) :
    prismSectionZero X ≫ (X ◁ stdSimplex.δ 1) = prismSectionAt X 0 := by
  rw [show stdSimplex.δ (1 : Fin 2) =
        stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) from
      stdSimplex.δ_one_eq_const, prismSectionZero, prismSectionAt,
    Category.assoc, ← MonoidalCategory.whiskerLeft_comp]

/-- Restricting a prism along `X ◁ stdSimplex.δ 0` and then reading the
endpoint is precomposition with the section at vertex `1`. -/
lemma prismSectionZero_whiskerLeft_δ_zero (X : SSet.{u}) :
    prismSectionZero X ≫ (X ◁ stdSimplex.δ 0) = prismSectionAt X 1 := by
  rw [show stdSimplex.δ (0 : Fin 2) =
        stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) from
      stdSimplex.δ_zero_eq_const, prismSectionZero, prismSectionAt,
    Category.assoc, ← MonoidalCategory.whiskerLeft_comp]

/-- First component of a right whiskering applied to a simplex. -/
@[simp]
lemma whiskerRight_app_apply_fst {X Y L : SSet.{u}} (f : X ⟶ Y)
    {Δ : SimplexCategoryᵒᵖ} (z : (X ⊗ L).obj Δ) :
    ((f ▷ L).app Δ z).1 = f.app Δ z.1 :=
  rfl

/-- Second component of a right whiskering applied to a simplex. -/
@[simp]
lemma whiskerRight_app_apply_snd {X Y L : SSet.{u}} (f : X ⟶ Y)
    {Δ : SimplexCategoryᵒᵖ} (z : (X ⊗ L).obj Δ) :
    ((f ▷ L).app Δ z).2 = z.2 :=
  rfl

/-- The prism simplex of the first-projection prism is the degeneracy
of the corresponding vertex. -/
lemma ihomSimplexOfPrism_fst (g : X ⟶ C) :
    ihomSimplexOfPrism (CartesianMonoidalCategory.fst X Δ[1] ≫ g) =
      ((ihom X).obj C).σ 0 (ihomVertexEquiv X C g) := by
  let canon : X ⊗ Δ[0] ⟶ X := (X ◁ Δ0IsoUnit.hom) ≫ (ρ_ X).hom
  have hsec : prismSectionZero X ≫ canon = 𝟙 X := by
    simp only [prismSectionZero, canon, Category.assoc]
    rw [← Category.assoc (X ◁ Δ0IsoUnit.inv) (X ◁ Δ0IsoUnit.hom)
      ((ρ_ X).hom), ← MonoidalCategory.whiskerLeft_comp,
      Δ0IsoUnit.inv_hom_id, MonoidalCategory.whiskerLeft_id]
    simp
  have hv : ihomVertexEquiv X C g = ihomSimplexOfPrism (canon ≫ g) := by
    rw [ihomSimplexOfPrism_zero, ← Category.assoc, hsec, Category.id_comp]
  have hprism : (X ◁ stdSimplex.σ 0) ≫ canon =
      CartesianMonoidalCategory.fst X Δ[1] := by
    apply NatTrans.ext
    funext Δ
    apply ConcreteCategory.hom_ext
    intro Z
    obtain ⟨Z₁, Z₂⟩ := Z
    rfl
  rw [hv, σ_ihomSimplexOfPrism, ← Category.assoc, hprism]

/-- The source face of a composite prism simplex, expressed through
the section at vertex `0`. -/
lemma δ_one_ihomSimplexOfPrism_comp {Y : SSet.{u}}
    (Ψ : X ⊗ Δ[1] ⟶ Y) (P : Y ⟶ C) :
    ((ihom X).obj C).δ 1 (ihomSimplexOfPrism (Ψ ≫ P)) =
      ihomVertexEquiv X C ((prismSectionAt X 0 ≫ Ψ) ≫ P) := by
  rw [δ_one_ihomSimplexOfPrism]
  congr 1

/-- The target face of a composite prism simplex, expressed through
the section at vertex `1`. -/
lemma δ_zero_ihomSimplexOfPrism_comp {Y : SSet.{u}}
    (Ψ : X ⊗ Δ[1] ⟶ Y) (P : Y ⟶ C) :
    ((ihom X).obj C).δ 0 (ihomSimplexOfPrism (Ψ ≫ P)) =
      ihomVertexEquiv X C ((prismSectionAt X 1 ≫ Ψ) ≫ P) := by
  rw [δ_zero_ihomSimplexOfPrism]
  congr 1

end SSet
