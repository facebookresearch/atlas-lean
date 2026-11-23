/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.Target
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Identity-span reflection in the actual extension fiber

A raw representative of an arrow in the strict fiber of the given-quotient
target maps to the identity span class. Its endpoint equalities transport its
quotient legs to the given object. The quotient relation identifies both legs
with an apex isomorphism. Kernel comparison and an admissible zero-cokernel
argument give the reverse kernel and forward middle isomorphisms.

The inverse admissible-mono factorization reconstructs a raw inverse diagram.
Both quotient-category and strict-fiber inverse laws retain the literal target
identity. The full statement covers every raw representative, and its derived
IsIso instance makes the standard inverse interface available to callers.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.ExactCategory Limits AlgebraicKTheory Opposite
open CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

universe u v

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

variable {E' E : ExtensionCategory C}

private theorem identity_span_legs {X : C} (S : QuillenSpan X X)
    (h : QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨X⟩) S = 𝟙 (⟨X⟩ : QuillenQ C)) :
    S.l = S.r ∧ IsIso S.l ∧ IsIso S.r := by
  obtain ⟨e⟩ := (QuillenQ.mkHom_eq_iff (X := ⟨X⟩) (Y := ⟨X⟩)
    (S₁ := S) (S₂ := (Span.id X : QuillenSpan X X))).mp
      (h.trans (show (𝟙 (⟨X⟩ : QuillenQ C)) = QuillenQ.mkHom (Span.id X) from rfl))
  let a := apexIsoOfSpanIso e
  have hl : a.hom = S.l := by
    change e.hom.hom = S.l
    have he := e.hom.hom_l
    change e.hom.hom ≫ 𝟙 X = S.l at he
    exact (Category.comp_id e.hom.hom).symm.trans he
  have hr : a.hom = S.r := by
    change e.hom.hom = S.r
    have he := e.hom.hom_r
    change e.hom.hom ≫ 𝟙 X = S.r at he
    exact (Category.comp_id e.hom.hom).symm.trans he
  refine ⟨hl.symm.trans hr, ?_, ?_⟩
  · rw [← hl]
    infer_instance
  · rw [← hr]
    infer_instance

private theorem fiber_representative_legs (X : C)
    {a b : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : a ⟶ b) (d : ExtensionDiagram a.val b.val)
    (hd : ExtensionCategory.mkHom d = f.val) :
    d.lambda ≫ eqToHom (congrArg QuillenQ.obj a.property) =
        d.mu ≫ eqToHom (congrArg QuillenQ.obj b.property) ∧
      IsIso d.lambda ∧ IsIso d.mu := by
  rcases a with ⟨⟨@⟨A', B', X', i', p', w'⟩, he'⟩, hx'⟩
  rcases b with ⟨⟨@⟨A, B, X'', i, p, w⟩, he⟩, hx⟩
  have hX' : X' = X := congrArg QuillenQ.obj hx'
  have hX : X'' = X := congrArg QuillenQ.obj hx
  subst X' X''
  let _ : Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) (ExtensionCategory.mkHom d) := by
    rw [hd]
    exact f.property
  have hmap : (ExtensionCategory.target (C := C)).map (ExtensionCategory.mkHom d) =
      𝟙 (⟨X⟩ : QuillenQ C) :=
    (IsHomLift.eq_of_isHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) (ExtensionCategory.mkHom d)).symm
  rw [ExtensionCategory.target_map_mkHom] at hmap
  have hlegs := identity_span_legs d.toQuillenSpan hmap
  refine ⟨?_, hlegs.2.1, hlegs.2.2⟩
  change d.lambda ≫ 𝟙 X = d.mu ≫ 𝟙 X
  exact (Category.comp_id d.lambda).trans (hlegs.1.trans (Category.comp_id d.mu).symm)

private def kernelComparison (d : ExtensionDiagram E' E) [IsIso d.lambda] :
    {e : E.row.X₁ ≅ E'.row.X₁ // e.hom = d.alpha ∧ e.inv ≫ d.j = E'.row.f} := by
  letI : Mono E'.row.f := (isAdmissibleMono_f E'.admissible).mono
  letI : Mono d.j := (isAdmissibleMono_f d.admissible).mono
  have hz : E'.row.f ≫ d.q = 0 := by
    apply (cancel_mono d.lambda).1
    rw [zero_comp, Category.assoc, d.q_lambda]
    exact E'.row.zero
  let k := KernelFork.IsLimit.lift'
    (isLimit_kernelFork_of_isAdmissibleExact d.admissible) E'.row.f hz
  have hk : k.val ≫ d.j = E'.row.f := k.property
  refine ⟨{ hom := d.alpha, inv := k.val, hom_inv_id := ?_, inv_hom_id := ?_ }, rfl, hk⟩
  · apply (cancel_mono d.j).1
    rw [Category.assoc, hk, ← d.j_eq, Category.id_comp]
  · apply (cancel_mono E'.row.f).1
    rw [Category.assoc, ← d.j_eq, hk, Category.id_comp]

private theorem beta_isIso (d : ExtensionDiagram E' E) [IsIso d.mu] : IsIso d.beta := by
  let _ : Epi d.q := (isAdmissibleEpi_g d.admissible).epi
  obtain ⟨Z, c, w, he⟩ := d.beta_admissible
  have hz : E.row.f ≫ c = 0 := by
    rw [← d.j_beta, Category.assoc, w, comp_zero]
  let k := CokernelCofork.IsColimit.desc'
    (isColimit_cokernelCofork_of_isAdmissibleExact E.admissible) c hz
  have hk : E.row.g ≫ k.val = c := k.property
  have hk0 : k.val = 0 := by
    apply (cancel_epi (d.q ≫ d.mu)).1
    rw [comp_zero, d.q_mu, Category.assoc, hk, w]
  have hc : c = 0 := by rw [← hk, hk0, comp_zero]
  exact KernelFork.IsLimit.isIso_ι (KernelFork.ofι d.beta w)
    (isLimit_kernelFork_of_isAdmissibleExact he) hc

private def inverseNormalization (d : ExtensionDiagram E' E)
    [IsIso d.alpha] [IsIso d.beta] : E.subdivisionObj ⟶ E'.subdivisionObj :=
  SegalSubdivision.homMk (AdmissibleMonoCategory (C := C))
    (⟨inv d.alpha, IsAdmissibleMono.of_isIso _⟩ :
      (⟨E'.row.X₁⟩ : AdmissibleMonoCategory (C := C)) ⟶ ⟨E.row.X₁⟩)
    (⟨inv d.beta, IsAdmissibleMono.of_isIso _⟩ :
      (⟨E.row.X₂⟩ : AdmissibleMonoCategory (C := C)) ⟶ ⟨E'.row.X₂⟩) (by
        apply InducedWideCategory.Hom.ext
        change inv d.alpha ≫ E.row.f ≫ inv d.beta = E'.row.f
        rw [← d.j_beta, d.j_eq]
        simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id, Category.comp_id])

private def inverseDiagram (d : ExtensionDiagram E' E) [IsIso d.alpha] [IsIso d.beta] :
    ExtensionDiagram E E' :=
  ExtensionDiagram.ofNormalization (inverseNormalization d)

private theorem hom_inverseDiagram (d : ExtensionDiagram E' E)
    [IsIso d.alpha] [IsIso d.beta] :
    ExtensionCategory.mkHom d ≫ ExtensionCategory.mkHom (inverseDiagram d) = 𝟙 E' := by
  apply ExtensionCategory.homNormalization.injective
  simp only [ExtensionCategory.homNormalization_comp, ExtensionCategory.homNormalization_mkHom,
    ExtensionCategory.homNormalization_id, inverseDiagram,
    ExtensionDiagram.normalize_ofNormalization]
  apply Functor.Elements.hom_ext
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    apply InducedWideCategory.Hom.ext
    change inv d.alpha ≫ d.alpha = 𝟙 _
    exact IsIso.inv_hom_id d.alpha
  · apply InducedWideCategory.Hom.ext
    change d.beta ≫ inv d.beta = 𝟙 _
    exact IsIso.hom_inv_id d.beta

private theorem inverseDiagram_hom (d : ExtensionDiagram E' E)
    [IsIso d.alpha] [IsIso d.beta] :
    ExtensionCategory.mkHom (inverseDiagram d) ≫ ExtensionCategory.mkHom d = 𝟙 E := by
  apply ExtensionCategory.homNormalization.injective
  simp only [ExtensionCategory.homNormalization_comp, ExtensionCategory.homNormalization_mkHom,
    ExtensionCategory.homNormalization_id, inverseDiagram,
    ExtensionDiagram.normalize_ofNormalization]
  apply Functor.Elements.hom_ext
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    apply InducedWideCategory.Hom.ext
    change d.alpha ≫ inv d.alpha = 𝟙 _
    exact IsIso.hom_inv_id d.alpha
  · apply InducedWideCategory.Hom.ext
    change inv d.beta ≫ d.beta = 𝟙 _
    exact IsIso.inv_hom_id d.beta

/-- The full original identity-span reflection and inverse construction for
every actual strict-fiber arrow and every raw quotient-diagram representative. -/
theorem fiber_identity_span_reflection (X : C)
    {a b : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : a ⟶ b) (d : ExtensionDiagram a.val b.val)
    (hd : ExtensionCategory.mkHom d = f.val) :
    d.lambda ≫ eqToHom (congrArg QuillenQ.obj a.property) =
        d.mu ≫ eqToHom (congrArg QuillenQ.obj b.property) ∧
    IsIso d.lambda ∧ IsIso d.mu ∧ IsIso d.alpha ∧ IsIso d.beta ∧
    ∃ (eα : b.val.row.X₁ ≅ a.val.row.X₁) (di : ExtensionDiagram b.val a.val) (g : b ⟶ a),
      eα.hom = d.alpha ∧ eα.inv ≫ d.j = a.val.row.f ∧
      g.val = ExtensionCategory.mkHom di ∧
      ExtensionCategory.mkHom d ≫ ExtensionCategory.mkHom di = 𝟙 a.val ∧
      ExtensionCategory.mkHom di ≫ ExtensionCategory.mkHom d = 𝟙 b.val ∧
      Functor.IsHomLift (ExtensionCategory.target (C := C))
        (𝟙 (⟨X⟩ : QuillenQ C)) (ExtensionCategory.mkHom di) ∧
      f ≫ g = 𝟙 a ∧ g ≫ f = 𝟙 b := by
  obtain ⟨heq, hLambda, hMu⟩ := fiber_representative_legs X f d hd
  let _ : IsIso d.lambda := hLambda
  let _ : IsIso d.mu := hMu
  let aComparison := kernelComparison d
  let _ : IsIso d.alpha := aComparison.property.1 ▸ (inferInstance : IsIso aComparison.val.hom)
  let _ : IsIso d.beta := beta_isIso d
  let di := inverseDiagram d
  have hleft : ExtensionCategory.mkHom d ≫ ExtensionCategory.mkHom di = 𝟙 a.val :=
    hom_inverseDiagram d
  have hright : ExtensionCategory.mkHom di ≫ ExtensionCategory.mkHom d = 𝟙 b.val :=
    inverseDiagram_hom d
  let e : a.val ≅ b.val :=
    { hom := ExtensionCategory.mkHom d, inv := ExtensionCategory.mkHom di,
      hom_inv_id := hleft, inv_hom_id := hright }
  let _ : Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) e.hom := by
    change Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) (ExtensionCategory.mkHom d)
    rw [hd]
    exact f.property
  have hinverse : Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) (ExtensionCategory.mkHom di) := by
    change Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) e.inv
    exact IsHomLift.lift_id_inv (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C) e
  let g : b ⟶ a := ⟨ExtensionCategory.mkHom di, hinverse⟩
  refine ⟨heq, hLambda, hMu, inferInstance, inferInstance, aComparison.val, di, g,
    aComparison.property.1, aComparison.property.2, rfl, hleft, hright, hinverse, ?_, ?_⟩
  · apply Subtype.ext
    change f.val ≫ ExtensionCategory.mkHom di = 𝟙 a.val
    rw [← hd]
    exact hleft
  · apply Subtype.ext
    change ExtensionCategory.mkHom di ≫ f.val = 𝟙 b.val
    rw [← hd]
    exact hright

/-- Every morphism in the actual target fiber is invertible by the raw diagram construction. -/
instance fiber_morphism_isIso (X : C)
    {a b : Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C)}
    (f : a ⟶ b) : IsIso f := by
  obtain ⟨d, hd⟩ := Quotient.exists_rep f.val
  obtain ⟨_, _, _, _, _, eα, di, g, _, _, _, _, _, _, hfg, hgf⟩ :=
    fiber_identity_span_reflection X f d hd
  exact ⟨⟨g, hfg, hgf⟩⟩

end AlgebraicKTheory.ExtensionCategory

end
