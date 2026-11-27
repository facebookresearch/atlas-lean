/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Rigidity
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Stability
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFibrationHomotopyExtension
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexFirstContraction
public import MathlibExt.CategoryTheory.TrivialBundleWithFiberTerminal
public import MathlibExt.CategoryTheory.TrivialBundleWithFiberIso

/-!
# Pullback rigidity and fixed fibers over standard simplices

Let p:E→B be a minimal Kan fibration. For a directed homotopy f₀→f₁ of maps A→B, any pullback
presentations over f₀,f₁ are isomorphic over A. In particular, endpoint pullbacks over B×Δ[1]
are isomorphic over B.

A minimal fibration over Δ[n] has a product presentation with its strict fiber over the first
vertex, commuting with the projection to Δ[n]. All simplicial sets may lie in any universe u.

The mathematical construction follows Joël Riou's minimal-fibration argument. Reference:
Goerss–Jardine, Simplicial Homotopy Theory, Chapter I, Section 10.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial SSet HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet
namespace MinimalFibration

/-- For a simplicial homotopy H:f→g between maps X→Y and any simplicial set Z, the cylinder
((z,x),t)↦(z,H(x,t)) is a homotopy Z×f→Z×g. -/
private noncomputable def whiskerLeftHomotopy
    {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (Z : SSet.{u}) :
    SSet.Homotopy (Z ◁ f) (Z ◁ g) where
  h := (α_ Z X (Δ[1] : SSet.{u})).hom ≫ Z ◁ H.h
  h₀ := by
    change ι₀ ≫ (α_ Z X (Δ[1] : SSet.{u})).hom ≫ Z ◁ H.h = Z ◁ f
    calc
      ι₀ ≫ (α_ Z X (Δ[1] : SSet.{u})).hom ≫ Z ◁ H.h = Z ◁ (ι₀ ≫ H.h) := rfl
      _ = Z ◁ f := by rw [H.h₀]
  h₁ := by
    change ι₁ ≫ (α_ Z X (Δ[1] : SSet.{u})).hom ≫ Z ◁ H.h = Z ◁ g
    calc
      ι₁ ≫ (α_ Z X (Δ[1] : SSet.{u})).hom ≫ Z ◁ H.h = Z ◁ (ι₁ ≫ H.h) := rfl
      _ = Z ◁ g := by rw [H.h₁]
  rel := by ext m ⟨⟨x, hx⟩, t⟩ <;> cases hx

/-- For any simplicial set B, the cylinder B×Δ[1] has a directed homotopy from projection to B
followed by its endpoint-zero inclusion to the identity of B×Δ[1]. -/
private noncomputable def endpointZeroBaseHomotopy (B : SSet.{u}) :
    SSet.Homotopy
      (fst B (Δ[1] : SSet.{u}) ≫ SSet.ι₀)
      (𝟙 (B ⊗ (Δ[1] : SSet.{u}))) where
  h := (whiskerLeftHomotopy
    (SSet.stdSimplex.homotopyConstFirstId.{u} 1) B).h
  h₀ := by
    rw [(whiskerLeftHomotopy
      (SSet.stdSimplex.homotopyConstFirstId.{u} 1) B).h₀]
    ext <;> simp
  h₁ := by
    rw [(whiskerLeftHomotopy
      (SSet.stdSimplex.homotopyConstFirstId.{u} 1) B).h₁]
    simp
  rel := by ext m ⟨⟨x, hx⟩, t⟩ <;> cases hx

/-- For any simplicial set B, the cylinder B×Δ[1] has a directed homotopy from identity to
projection followed by the endpoint-one inclusion. -/
private noncomputable def endpointOneBaseHomotopy (B : SSet.{u}) :
    SSet.Homotopy
      (𝟙 (B ⊗ (Δ[1] : SSet.{u})))
      (fst B (Δ[1] : SSet.{u}) ≫ SSet.ι₁) where
  h := (whiskerLeftHomotopy
    (SSet.stdSimplex.homotopyIdConstLast.{u} 1) B).h
  h₀ := by
    rw [(whiskerLeftHomotopy
      (SSet.stdSimplex.homotopyIdConstLast.{u} 1) B).h₀]
    simp
  h₁ := by
    rw [(whiskerLeftHomotopy
      (SSet.stdSimplex.homotopyIdConstLast.{u} 1) B).h₁]
    ext <;> simp
  rel := by ext m ⟨⟨x, hx⟩, t⟩ <;> cases hx

private lemma endpointZeroBaseHomotopy_fst (B : SSet.{u}) :
    (endpointZeroBaseHomotopy B).h ≫ fst B (Δ[1] : SSet.{u}) =
      fst (B ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) ≫
        fst B (Δ[1] : SSet.{u}) := by
  simp only [endpointZeroBaseHomotopy, whiskerLeftHomotopy, Category.assoc,
    whiskerLeft_fst, associator_hom_fst]

private lemma endpointOneBaseHomotopy_fst (B : SSet.{u}) :
    (endpointOneBaseHomotopy B).h ≫ fst B (Δ[1] : SSet.{u}) =
      fst (B ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) ≫
        fst B (Δ[1] : SSet.{u}) := by
  simp only [endpointOneBaseHomotopy, whiskerLeftHomotopy, Category.assoc,
    whiskerLeft_fst, associator_hom_fst]

/-- After swapping the two interval factors, the last-vertex contraction of Δ[1] keeps the
vertex-one endpoint fixed throughout the remaining interval. -/
private lemma lastEndpointBraiding :
    SSet.ι₁ ≫ (β_ _ _).hom ≫
        (SSet.stdSimplex.homotopyIdConstLast.{u} 1).h =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  ext i : 1
  change SSet.stdSimplex.asOrderHom
      ((SSet.stdSimplex.homotopyIdConstLast.{u} 1).h.app (Opposite.op ⦋1⦌)
        ⟨_, _⟩) i = _
  rw [SSet.stdSimplex.homotopyIdConstLast_h_app_apply]
  fin_cases i <;> rfl

private lemma endpointZeroBaseHomotopy_fixed (B : SSet.{u}) :
    (SSet.ι₀ ▷ (Δ[1] : SSet.{u})) ≫ (endpointZeroBaseHomotopy B).h =
      fst B (Δ[1] : SSet.{u}) ≫ SSet.ι₀ := by
  change B ◁ (SSet.ι₀ ≫ (β_ _ _).hom ≫
    (SSet.stdSimplex.homotopyConstFirstId.{u} 1).h) = _
  rw [SSet.stdSimplex.ι₀_β_hom_homotopyConstFirstId_h]
  rfl

private lemma endpointOneBaseHomotopy_fixed (B : SSet.{u}) :
    (SSet.ι₁ ▷ (Δ[1] : SSet.{u})) ≫ (endpointOneBaseHomotopy B).h =
      fst B (Δ[1] : SSet.{u}) ≫ SSet.ι₁ := by
  change B ◁ (SSet.ι₁ ≫ (β_ _ _).hom ≫
    (SSet.stdSimplex.homotopyIdConstLast.{u} 1).h) = _
  rw [lastEndpointBraiding]
  rfl

/-- For maps p:E→B, j:A→B, r:B→A, i:E′→E and p′:E′→A with a base homotopy id_B→r≫j, forward lift
data consist of a retraction q:E→E′ with i≫q=id_E′, a homotopy id_E→q≫i projecting to the base
homotopy, and q≫p′=p≫r. -/
private structure ForwardLiftData
    {E A B E' : SSet.{u}}
    (p : E ⟶ B) (j : A ⟶ B) (r : B ⟶ A)
    (h : SSet.Homotopy (𝟙 B) (r ≫ j))
    (i : E' ⟶ E) (p' : E' ⟶ A) where
  retraction : E ⟶ E'
  retract_eq : i ≫ retraction = 𝟙 E'
  homotopy : SSet.Homotopy (𝟙 E) (retraction ≫ i)
  homotopy_base : homotopy.h ≫ p =
    (p ▷ (Δ[1] : SSet.{u})) ≫ h.h
  retraction_base : retraction ≫ p' = p ≫ r

/-- For maps p:E→B, j:A→B, r:B→A, i:E′→E and p′:E′→A with a base homotopy r≫j→id_B, backward lift
data consist of a retraction q with i≫q=id_E′, a homotopy q≫i→id_E projecting to the base
homotopy, and q≫p′=p≫r. -/
private structure BackwardLiftData
    {E A B E' : SSet.{u}}
    (p : E ⟶ B) (j : A ⟶ B) (r : B ⟶ A)
    (h : SSet.Homotopy (r ≫ j) (𝟙 B))
    (i : E' ⟶ E) (p' : E' ⟶ A) where
  retraction : E ⟶ E'
  retract_eq : i ≫ retraction = 𝟙 E'
  homotopy : SSet.Homotopy (retraction ≫ i) (𝟙 E)
  homotopy_base : homotopy.h ≫ p =
    (p ▷ (Δ[1] : SSet.{u})) ≫ h.h
  retraction_base : retraction ≫ p' = p ≫ r

private theorem nonempty_forwardLiftData
    {E A B E' : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (j : A ⟶ B) (r : B ⟶ A) (hretract : j ≫ r = 𝟙 A)
    (h : SSet.Homotopy (𝟙 B) (r ≫ j))
    (hfixed : (j ▷ (Δ[1] : SSet.{u})) ≫ h.h =
      fst A (Δ[1] : SSet.{u}) ≫ j)
    {i : E' ⟶ E} {p' : E' ⟶ A}
    (sq : IsPullback i p' p j) :
    Nonempty (ForwardLiftData p j r h i p') := by
  let _ : Mono i :=
    MorphismProperty.of_isPullback (P := .monomorphisms _) sq.flip
      (mono_of_mono_fac hretract)
  obtain ⟨φ, hφ₀, hφi, hφp⟩ :=
    homotopy_extension_property₀ i p (fst _ _ ≫ i) (𝟙 E) (by simp)
      ((p ▷ (Δ[1] : SSet.{u})) ≫ h.h) (by simp) (by
        rw [← comp_whiskerRight_assoc, sq.w, comp_whiskerRight_assoc, hfixed,
          whiskerRight_fst_assoc, Category.assoc, sq.w])
  obtain ⟨l, hli, hlp'⟩ := sq.exists_lift (ι₁ ≫ φ) (p ≫ r) (by
    rw [Category.assoc, hφp, ι₁_comp_assoc, h.h₁, Category.assoc])
  refine ⟨{
    retraction := l
    retract_eq := ?_
    homotopy := {
      h := φ
      h₀ := hφ₀
      h₁ := hli.symm
      rel := by ext m ⟨⟨x, hx⟩, t⟩; cases hx }
    homotopy_base := hφp
    retraction_base := hlp' }⟩
  rw [← cancel_mono i, Category.assoc, hli, ← ι₁_comp_assoc, hφi,
    ι₁_fst_assoc, Category.id_comp]

private theorem nonempty_backwardLiftData
    {E A B E' : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (j : A ⟶ B) (r : B ⟶ A) (hretract : j ≫ r = 𝟙 A)
    (h : SSet.Homotopy (r ≫ j) (𝟙 B))
    (hfixed : (j ▷ (Δ[1] : SSet.{u})) ≫ h.h =
      fst A (Δ[1] : SSet.{u}) ≫ j)
    {i : E' ⟶ E} {p' : E' ⟶ A}
    (sq : IsPullback i p' p j) :
    Nonempty (BackwardLiftData p j r h i p') := by
  let _ : Mono i :=
    MorphismProperty.of_isPullback (P := .monomorphisms _) sq.flip
      (mono_of_mono_fac hretract)
  obtain ⟨φ, hφ₁, hφi, hφp⟩ :=
    homotopy_extension_property₁ i p (fst _ _ ≫ i) (𝟙 E) (by simp)
      ((p ▷ (Δ[1] : SSet.{u})) ≫ h.h) (by simp) (by
        rw [← comp_whiskerRight_assoc, sq.w, comp_whiskerRight_assoc, hfixed,
          whiskerRight_fst_assoc, Category.assoc, sq.w])
  obtain ⟨l, hli, hlp'⟩ := sq.exists_lift (ι₀ ≫ φ) (p ≫ r) (by
    rw [Category.assoc, hφp, ι₀_comp_assoc, h.h₀, Category.assoc])
  refine ⟨{
    retraction := l
    retract_eq := ?_
    homotopy := {
      h := φ
      h₀ := hli.symm
      h₁ := hφ₁
      rel := by ext m ⟨⟨x, hx⟩, t⟩; cases hx }
    homotopy_base := hφp
    retraction_base := hlp' }⟩
  rw [← cancel_mono i, Category.assoc, hli, ← ι₀_comp_assoc, hφi,
    ι₀_fst_assoc, Category.id_comp]

/-- For a Kan fibration p:X→B and a map-level fiberwise homotopy f→g over p, choose the reversed
fiberwise homotopy g→f. -/
private noncomputable def reverseFiberwiseHomotopy
    {X B : SSet.{u}} {p : X ⟶ B} [Fibration p]
    {f g : X ⟶ X} (H : SSet.FiberwiseHomotopy p p f g) :
    SSet.FiberwiseHomotopy p p g f := by
  let R : SSet.HomotopyRelOver p f g (⊥ : X.Subcomplex) :=
    { toHomotopyRel :=
        { h := H.hom.h
          h₀ := H.hom.h₀
          h₁ := H.hom.h₁
          stationary := by intro m x hx t; cases hx }
      over := by simpa only [H.fac₀] using H.over }
  let R' := R.symm
  exact
    { hom := R'.toHomotopyRel.toHomotopy
      over := by
        change R'.toHomotopyRel.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ p
        simpa only [H.fac₁] using R'.over }

/-- For a minimal Kan fibration E→B×Δ[1], two exhibited pullbacks E₀,E₁ over the endpoint inclusions
B→B×Δ[1] are isomorphic over B. -/
private theorem exists_iso_pullback_endpoints
    {E B E₀ E₁ : SSet.{u}}
    (p : E ⟶ B ⊗ (Δ[1] : SSet.{u}))
    (hp : IsMinimalFibration p)
    {j₀ : E₀ ⟶ E} {p₀ : E₀ ⟶ B}
    (sq₀ : IsPullback j₀ p₀ p SSet.ι₀)
    {j₁ : E₁ ⟶ E} {p₁ : E₁ ⟶ B}
    (sq₁ : IsPullback j₁ p₁ p SSet.ι₁) :
    ∃ e : E₀ ≅ E₁, e.hom ≫ p₁ = p₀ := by
  let _ : Fibration p := hp.1
  have hp₀ : IsMinimalFibration p₀ := isMinimalFibration_of_isPullback sq₀ hp
  have hp₁ : IsMinimalFibration p₁ := isMinimalFibration_of_isPullback sq₁ hp
  let r : B ⊗ (Δ[1] : SSet.{u}) ⟶ B := fst _ _
  let base₀ := endpointZeroBaseHomotopy B
  let base₁ := endpointOneBaseHomotopy B
  obtain ⟨L₀⟩ := nonempty_backwardLiftData p SSet.ι₀ r (by simp [r]) base₀
    (endpointZeroBaseHomotopy_fixed B) sq₀
  obtain ⟨L₁⟩ := nonempty_forwardLiftData p SSet.ι₁ r (by simp [r]) base₁
    (endpointOneBaseHomotopy_fixed B) sq₁
  let f : E₀ ⟶ E₁ := j₀ ≫ L₁.retraction
  let g : E₁ ⟶ E₀ := j₁ ≫ L₀.retraction
  let K₀ : E₀ ⊗ (Δ[1] : SSet.{u}) ⟶ E₀ :=
    (j₀ ▷ (Δ[1] : SSet.{u})) ≫ L₁.homotopy.h ≫ L₀.retraction
  let K₁ : E₁ ⊗ (Δ[1] : SSet.{u}) ⟶ E₁ :=
    (j₁ ▷ (Δ[1] : SSet.{u})) ≫ L₀.homotopy.h ≫ L₁.retraction
  have hK₀_zero : ι₀ ≫ K₀ = 𝟙 E₀ := by
    calc
      ι₀ ≫ K₀ = j₀ ≫ (ι₀ ≫ L₁.homotopy.h) ≫ L₀.retraction := by
        simp only [K₀, ι₀_comp_assoc, Category.assoc]
      _ = j₀ ≫ (𝟙 E) ≫ L₀.retraction := by rw [L₁.homotopy.h₀]
      _ = j₀ ≫ L₀.retraction := by simp
      _ = 𝟙 E₀ := L₀.retract_eq
  have hK₀_one : ι₁ ≫ K₀ = f ≫ g := by
    calc
      ι₁ ≫ K₀ = j₀ ≫ (ι₁ ≫ L₁.homotopy.h) ≫ L₀.retraction := by
        simp only [K₀, ι₁_comp_assoc, Category.assoc]
      _ = j₀ ≫ (L₁.retraction ≫ j₁) ≫ L₀.retraction := by
        rw [L₁.homotopy.h₁]
      _ = f ≫ g := by simp only [f, g, Category.assoc]
  have hK₀_over : K₀ ≫ p₀ = fst E₀ (Δ[1] : SSet.{u}) ≫ p₀ := by
    calc
      K₀ ≫ p₀ = (j₀ ▷ (Δ[1] : SSet.{u})) ≫ L₁.homotopy.h ≫
          (L₀.retraction ≫ p₀) := by simp only [K₀, Category.assoc]
      _ = (j₀ ▷ (Δ[1] : SSet.{u})) ≫ L₁.homotopy.h ≫ (p ≫ r) := by
        rw [L₀.retraction_base]
      _ = (j₀ ▷ (Δ[1] : SSet.{u})) ≫ (L₁.homotopy.h ≫ p) ≫ r := by
        simp only [Category.assoc]
      _ = (j₀ ▷ (Δ[1] : SSet.{u})) ≫
          ((p ▷ (Δ[1] : SSet.{u})) ≫ base₁.h) ≫ r := by
        rw [L₁.homotopy_base]
      _ = ((j₀ ≫ p) ▷ (Δ[1] : SSet.{u})) ≫ base₁.h ≫ r := by
        simp only [Category.assoc, comp_whiskerRight]
      _ = ((p₀ ≫ SSet.ι₀) ▷ (Δ[1] : SSet.{u})) ≫ base₁.h ≫ r := by
        rw [sq₀.w]
      _ = (p₀ ▷ (Δ[1] : SSet.{u})) ≫
          (SSet.ι₀ ▷ (Δ[1] : SSet.{u})) ≫ base₁.h ≫ r := by
        simp only [Category.assoc, comp_whiskerRight]
      _ = (p₀ ▷ (Δ[1] : SSet.{u})) ≫
          (SSet.ι₀ ▷ (Δ[1] : SSet.{u})) ≫
            (fst (B ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) ≫ r) := by
        rw [endpointOneBaseHomotopy_fst]
      _ = (p₀ ▷ (Δ[1] : SSet.{u})) ≫ fst B (Δ[1] : SSet.{u}) ≫
          SSet.ι₀ ≫ r := by
        rw [whiskerRight_fst_assoc]
      _ = (p₀ ▷ (Δ[1] : SSet.{u})) ≫ fst B (Δ[1] : SSet.{u}) := by
        simp [r]
      _ = fst E₀ (Δ[1] : SSet.{u}) ≫ p₀ := by rw [whiskerRight_fst]
  have hK₁_zero : ι₀ ≫ K₁ = g ≫ f := by
    calc
      ι₀ ≫ K₁ = j₁ ≫ (ι₀ ≫ L₀.homotopy.h) ≫ L₁.retraction := by
        simp only [K₁, ι₀_comp_assoc, Category.assoc]
      _ = j₁ ≫ (L₀.retraction ≫ j₀) ≫ L₁.retraction := by
        rw [L₀.homotopy.h₀]
      _ = g ≫ f := by simp only [f, g, Category.assoc]
  have hK₁_one : ι₁ ≫ K₁ = 𝟙 E₁ := by
    calc
      ι₁ ≫ K₁ = j₁ ≫ (ι₁ ≫ L₀.homotopy.h) ≫ L₁.retraction := by
        simp only [K₁, ι₁_comp_assoc, Category.assoc]
      _ = j₁ ≫ (𝟙 E) ≫ L₁.retraction := by rw [L₀.homotopy.h₁]
      _ = j₁ ≫ L₁.retraction := by simp
      _ = 𝟙 E₁ := L₁.retract_eq
  have hK₁_over : K₁ ≫ p₁ = fst E₁ (Δ[1] : SSet.{u}) ≫ p₁ := by
    calc
      K₁ ≫ p₁ = (j₁ ▷ (Δ[1] : SSet.{u})) ≫ L₀.homotopy.h ≫
          (L₁.retraction ≫ p₁) := by simp only [K₁, Category.assoc]
      _ = (j₁ ▷ (Δ[1] : SSet.{u})) ≫ L₀.homotopy.h ≫ (p ≫ r) := by
        rw [L₁.retraction_base]
      _ = (j₁ ▷ (Δ[1] : SSet.{u})) ≫ (L₀.homotopy.h ≫ p) ≫ r := by
        simp only [Category.assoc]
      _ = (j₁ ▷ (Δ[1] : SSet.{u})) ≫
          ((p ▷ (Δ[1] : SSet.{u})) ≫ base₀.h) ≫ r := by
        rw [L₀.homotopy_base]
      _ = ((j₁ ≫ p) ▷ (Δ[1] : SSet.{u})) ≫ base₀.h ≫ r := by
        simp only [Category.assoc, comp_whiskerRight]
      _ = ((p₁ ≫ SSet.ι₁) ▷ (Δ[1] : SSet.{u})) ≫ base₀.h ≫ r := by
        rw [sq₁.w]
      _ = (p₁ ▷ (Δ[1] : SSet.{u})) ≫
          (SSet.ι₁ ▷ (Δ[1] : SSet.{u})) ≫ base₀.h ≫ r := by
        simp only [Category.assoc, comp_whiskerRight]
      _ = (p₁ ▷ (Δ[1] : SSet.{u})) ≫
          (SSet.ι₁ ▷ (Δ[1] : SSet.{u})) ≫
            (fst (B ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) ≫ r) := by
        rw [endpointZeroBaseHomotopy_fst]
      _ = (p₁ ▷ (Δ[1] : SSet.{u})) ≫ fst B (Δ[1] : SSet.{u}) ≫
          SSet.ι₁ ≫ r := by
        rw [whiskerRight_fst_assoc]
      _ = (p₁ ▷ (Δ[1] : SSet.{u})) ≫ fst B (Δ[1] : SSet.{u}) := by
        simp [r]
      _ = fst E₁ (Δ[1] : SSet.{u}) ≫ p₁ := by rw [whiskerRight_fst]
  let HfgForward : SSet.FiberwiseHomotopy p₀ p₀ (𝟙 E₀) (f ≫ g) :=
    { hom :=
        { h := K₀
          h₀ := hK₀_zero
          h₁ := hK₀_one
          rel := by ext m ⟨⟨x, hx⟩, t⟩; cases hx }
      over := hK₀_over }
  let _ : Fibration p₀ := hp₀.1
  let Hfg : SSet.FiberwiseHomotopy p₀ p₀ (f ≫ g) (𝟙 E₀) :=
    reverseFiberwiseHomotopy HfgForward
  let Hgf : SSet.FiberwiseHomotopy p₁ p₁ (g ≫ f) (𝟙 E₁) :=
    { hom :=
        { h := K₁
          h₀ := hK₁_zero
          h₁ := hK₁_one
          rel := by ext m ⟨⟨x, hx⟩, t⟩; cases hx }
      over := hK₁_over }
  let _ : IsIso f := isIso_of_fiberwiseHomotopyEquiv p₀ p₁ hp₀ hp₁ f g Hfg Hgf
  refine ⟨asIso f, ?_⟩
  change (j₀ ≫ L₁.retraction) ≫ p₁ = p₀
  calc
    (j₀ ≫ L₁.retraction) ≫ p₁ = j₀ ≫ (L₁.retraction ≫ p₁) := by
      rw [Category.assoc]
    _ = j₀ ≫ (p ≫ r) := by rw [L₁.retraction_base]
    _ = (j₀ ≫ p) ≫ r := by rw [Category.assoc]
    _ = (p₀ ≫ SSet.ι₀) ≫ r := by rw [sq₀.w]
    _ = p₀ := by simp [r]

/-- Let p:E→B be a minimal Kan fibration and H:f₀→f₁ a directed homotopy of maps A→B. For any
exhibited pullbacks E₀,E₁ over f₀,f₁ with projections p₀,p₁ to A, there is an isomorphism
e:E₀≅E₁ satisfying e≫p₁=p₀. -/
theorem exists_iso_pullback_of_homotopy
    {E A B E₀ E₁ : SSet.{u}} (p : E ⟶ B)
    (hp : IsMinimalFibration p)
    {f₀ f₁ : A ⟶ B} (H : SSet.Homotopy f₀ f₁)
    {p₀ : E₀ ⟶ A} {g₀ : E₀ ⟶ E}
    (sq₀ : IsPullback g₀ p₀ p f₀)
    {p₁ : E₁ ⟶ A} {g₁ : E₁ ⟶ E}
    (sq₁ : IsPullback g₁ p₁ p f₁) :
    ∃ e : E₀ ≅ E₁, e.hom ≫ p₁ = p₀ := by
  let q : Limits.pullback p H.h ⟶ A ⊗ (Δ[1] : SSet.{u}) :=
    Limits.pullback.snd p H.h
  have hpq : IsMinimalFibration q := isMinimalFibration_pullback_snd p H.h hp
  let j₀ : E₀ ⟶ Limits.pullback p H.h :=
    Limits.pullback.lift g₀ (p₀ ≫ SSet.ι₀) (by
      rw [sq₀.w, Category.assoc, H.h₀])
  let j₁ : E₁ ⟶ Limits.pullback p H.h :=
    Limits.pullback.lift g₁ (p₁ ≫ SSet.ι₁) (by
      rw [sq₁.w, Category.assoc, H.h₁])
  have sq₀' : IsPullback j₀ p₀ q SSet.ι₀ := by
    have hfst : j₀ ≫ Limits.pullback.fst p H.h = g₀ := by
      dsimp [j₀]
      rw [Limits.pullback.lift_fst]
    have outer : IsPullback (j₀ ≫ Limits.pullback.fst p H.h) p₀ p
        (SSet.ι₀ ≫ H.h) := by
      simpa only [hfst, H.h₀] using sq₀
    have comm : j₀ ≫ q = p₀ ≫ SSet.ι₀ := by
      dsimp [j₀, q]
      rw [Limits.pullback.lift_snd]
    exact IsPullback.of_right outer comm (IsPullback.of_hasPullback p H.h)
  have sq₁' : IsPullback j₁ p₁ q SSet.ι₁ := by
    have hfst : j₁ ≫ Limits.pullback.fst p H.h = g₁ := by
      dsimp [j₁]
      rw [Limits.pullback.lift_fst]
    have outer : IsPullback (j₁ ≫ Limits.pullback.fst p H.h) p₁ p
        (SSet.ι₁ ≫ H.h) := by
      simpa only [hfst, H.h₁] using sq₁
    have comm : j₁ ≫ q = p₁ ≫ SSet.ι₁ := by
      dsimp [j₁, q]
      rw [Limits.pullback.lift_snd]
    exact IsPullback.of_right outer comm (IsPullback.of_hasPullback p H.h)
  exact exists_iso_pullback_endpoints q hpq sq₀' sq₁'

/-- For a minimal Kan fibration p:E→Δ[n], take the strict fiber over the first vertex of Δ[n]. The
map p has a product presentation with this fixed fiber, commuting with its projection to Δ[n]. -/
noncomputable def trivialBundleWithFiber_stdSimplex
    {E : SSet.{u}} {n : ℕ} (p : E ⟶ Δ[n])
    (hp : IsMinimalFibration p) :
    CategoryTheory.TrivialBundleWithFiber
      (Limits.pullback p
        (SSet.const (X := (Δ[0] : SSet.{u}))
          (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) p := by
  let v₀ : (Δ[n] : SSet.{u}) _⦋0⦌ :=
    SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))
  let b₀ : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.const v₀
  let c₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] := SSet.const v₀
  let a : (Δ[n] : SSet.{u}) ⟶ Δ[0] := SSet.stdSimplex.isTerminalObj₀.from _
  have fac : a ≫ b₀ = c₀ := by simp [b₀, c₀]
  let p₀ : Limits.pullback p c₀ ⟶ Δ[n] := Limits.pullback.snd p c₀
  let h₀ : CategoryTheory.TrivialBundleWithFiber (Limits.pullback p b₀) p₀ :=
    CategoryTheory.TrivialBundleWithFiber.ofIsPullbackOfFac
      (IsPullback.of_hasPullback p c₀) SSet.stdSimplex.isTerminalObj₀ a b₀ fac
  let H : SSet.Homotopy c₀ (𝟙 (Δ[n] : SSet.{u})) := by
    simpa only [c₀, v₀] using SSet.stdSimplex.homotopyConstFirstId.{u} n
  let hcomp := exists_iso_pullback_of_homotopy p hp H
    (IsPullback.of_hasPullback p c₀) (IsPullback.id_horiz p)
  let e : Limits.pullback p c₀ ≅ E := hcomp.choose
  have he : e.hom ≫ p = p₀ := hcomp.choose_spec
  simpa only [b₀, v₀] using
    CategoryTheory.TrivialBundleWithFiber.ofIso_rev e he h₀

end MinimalFibration
end SSet
