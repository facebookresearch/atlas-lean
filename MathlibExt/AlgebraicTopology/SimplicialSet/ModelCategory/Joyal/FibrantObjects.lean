/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalFibrations
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.PrismSkeletal

/-!
# Fibrant objects for genuine categorical fibrations

The terminal map of a simplicial set is a categorical fibration exactly
when that simplicial set is a quasicategory. Here categorical fibrations
are defined by the right lifting property against monic weak categorical
equivalences.

The forward implication uses the categorical inner horn inclusions. For
the reverse implication, essential surjectivity on the homotopy category
of functor objects supplies an extension up to an isomorphism. An edge
representing that isomorphism gives an equivalence prism. Extending the
source-prescribed prism makes its target section a strict extension.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed
open scoped Simplicial

namespace SSet

/-- The terminal map is a genuine categorical fibration if and only if
its source is a quasicategory. -/
theorem categoricalFibrations.terminalFrom_iff_quasicategory (X : SSet.{u}) :
    categoricalFibrations (terminal.from X) ↔ Quasicategory X := by
  constructor
  · intro h
    apply quasicategory_of_hasLiftingProperty X terminalIsTerminal
    intro n i h0 hn
    exact (categoricalFibrations.mem_iff _).mp h (horn n i).ι
      inferInstance (categoricalEquivalences.horn_ι h0 hn)
  · intro hX
    let _ : Quasicategory X := hX
    rw [categoricalFibrations.mem_iff]
    intro A B i hi hw
    let _ : Mono i := hi
    constructor
    intro f g _
    let p := (hoFunctor.map ((pre i).app X)).toFunctor
    let _ : p.IsEquivalence := hw X hX
    obtain ⟨b, ⟨hb⟩⟩ := Functor.EssSurj.mem_essImage p
      (HomotopyCategory.mk (ihomVertexEquiv A X f))
    obtain ⟨b, rfl⟩ :=
      (HomotopyCategory.objEquiv (X := (ihom B).obj X)).symm.surjective b
    change HomotopyCategory.mk (((pre i).app X).app _ b) ≅
      HomotopyCategory.mk (ihomVertexEquiv A X f) at hb
    obtain ⟨e, he⟩ := Edge.exists_toHoHom_eq hb.hom
    have hequiv : e.IsEquivalence := by
      rw [Edge.isEquivalence_iff, he]
      infer_instance
    let bsharp : B ⟶ X := (ihomVertexEquiv B X).symm b
    let H : A ⊗ Δ[1] ⟶ X := ihomPrismOfSimplex e.edge
    have hsource : prismSectionAt A 0 ≫ H = i ≫ bsharp := by
      apply (ihomVertexEquiv A X).injective
      rw [ihomVertexEquiv_prismSectionAt_zero_comp,
        ihomSimplexOfPrism_ihomPrismOfSimplex, e.src_eq,
        ← ihomVertexEquiv_pre_app, Equiv.apply_symm_apply]
    obtain ⟨F, hrestrict, _, _⟩ := prismSrcExtension_of_mono i H bsharp hsource
      (prismOneVerticalsEquivalences_ihomPrismOfSimplex_of_isEquivalence e hequiv)
    refine ⟨prismSectionAt B 1 ≫ F, ?_, terminalIsTerminal.hom_ext _ _⟩
    calc
      i ≫ prismSectionAt B 1 ≫ F =
          (prismSectionAt A 1 ≫ (i ▷ Δ[1])) ≫ F := by
            rw [prismSectionAt_comp_whiskerRight, Category.assoc]
      _ = prismSectionAt A 1 ≫ H := by rw [Category.assoc, hrestrict]
      _ = f := by
        apply (ihomVertexEquiv A X).injective
        rw [ihomVertexEquiv_prismSectionAt_one_comp,
          ihomSimplexOfPrism_ihomPrismOfSimplex, e.tgt_eq]

end SSet
