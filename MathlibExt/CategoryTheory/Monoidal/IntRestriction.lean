/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntCompact

/-!
# Faithfulness of restriction along the Int embedding

Monoidal natural isomorphisms between strong monoidal functors out of Int are
uniquely determined by their components on the embedded source. Duality determines
the negative components, and tensor compatibility determines every object.
This is the faithfulness part of Joyal, Street and Verity, Traced monoidal
categories (1996), Proposition 5.2, https://doi.org/10.1017/S0305004100074338.
It does not assert existence of extensions of arbitrary transformations.
-/

@[expose] public section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

private theorem coevaluation_naturality (F G : C ⥤ D) [F.Monoidal] [G.Monoidal]
    (e : F ≅ G) [NatTrans.IsMonoidal e.hom] (X Y : C) [ExactPairing X Y] :
    (ExactPairing.map F X Y).coevaluation' ≫ (e.hom.app X ⊗ₘ e.hom.app Y) =
      (ExactPairing.map G X Y).coevaluation' := by
  change (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫ _ = ε G ≫ G.map (η_ X Y) ≫ δ G X Y
  have ht := NatTrans.IsMonoidal.tensor (τ := e.hom) X Y
  have hd : δ F X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) = e.hom.app (X ⊗ Y) ≫ δ G X Y := by
    rw [← cancel_epi (μ F X Y)]
    simpa only [Category.assoc, μ_δ, μ_δ_assoc, Category.id_comp, Category.comp_id] using
      congrArg (fun k => k ≫ δ G X Y) ht.symm
  simp only [Category.assoc, hd, e.hom.naturality_assoc,
    ← NatTrans.IsMonoidal.unit (τ := e.hom)]

private theorem paired_component_ext (F G : C ⥤ D) [F.Monoidal] [G.Monoidal]
    (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (X Y : C) [ExactPairing X Y] (h : e.hom.app X = i.hom.app X) :
    e.hom.app Y = i.hom.app Y := by
  let _ := ExactPairing.map F X Y
  have hη : η_ (F.obj X) (F.obj Y) ≫ F.obj X ◁ e.hom.app Y =
      η_ (F.obj X) (F.obj Y) ≫ F.obj X ◁ i.hom.app Y := by
    have he := coevaluation_naturality F G e X Y
    have hi := coevaluation_naturality F G i X Y
    rw [h] at he
    have heq := he.trans hi.symm
    rw [← cancel_mono (i.hom.app X ▷ G.obj Y)]
    simpa only [tensorHom_def', Category.assoc, ExactPairing.coevaluation] using heq
  have hm := congrArg (tensorLeftHomEquiv (𝟙_ D) (F.obj X) (F.obj Y) (G.obj Y)).symm hη
  simpa only [tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft,
    cancel_epi] using hm

namespace IntConstruction
variable [SymmetricCategory C] (T : SymmetricTrace C)

/-- Monoidal natural isomorphisms out of Int are determined on the embedded source.
The target only needs a monoidal structure; it need not itself be rigid or symmetric. -/
theorem monoidalIso_ext {F G : IntConstruction T ⥤ D} [F.Monoidal] [G.Monoidal]
    (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (h : ∀ A, e.hom.app ((embedding T).obj A) = i.hom.app ((embedding T).obj A)) : e = i := by
  have hn (A : C) : e.hom.app (⟨𝟙_ C, A⟩ : IntConstruction T) =
      i.hom.app (⟨𝟙_ C, A⟩ : IntConstruction T) := by
    let _ := positivePairing T A
    exact paired_component_ext F G e i (⟨A, 𝟙_ C⟩ : IntConstruction T) ⟨𝟙_ C, A⟩ (h A)
  have ht (A B : C) :
      e.hom.app ((⟨A, 𝟙_ C⟩ : IntConstruction T) ⊗ ⟨𝟙_ C, B⟩) =
        i.hom.app ((⟨A, 𝟙_ C⟩ : IntConstruction T) ⊗ ⟨𝟙_ C, B⟩) := by
    rw [← cancel_epi (μ F (⟨A, 𝟙_ C⟩ : IntConstruction T) ⟨𝟙_ C, B⟩)]
    rw [NatTrans.IsMonoidal.tensor, NatTrans.IsMonoidal.tensor, hn]
    change (_ ⊗ₘ _) ≫ _ = (_ ⊗ₘ _) ≫ _
    rw [show e.hom.app (⟨A, 𝟙_ C⟩ : IntConstruction T) =
      i.hom.app (⟨A, 𝟙_ C⟩ : IntConstruction T) from h A]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rw [← cancel_mono (G.map (decomposition T X).hom),
    ← e.hom.naturality, ← i.hom.naturality, ht]

/-- Restricting monoidal natural isomorphisms along the embedding is injective. -/
theorem monoidalIso_eq_of_whiskerLeft_eq {F G : IntConstruction T ⥤ D}
    [F.Monoidal] [G.Monoidal] (e i : F ≅ G)
    [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (h : Functor.isoWhiskerLeft (embedding T) e = Functor.isoWhiskerLeft (embedding T) i) :
    e = i := by
  apply monoidalIso_ext T e i
  intro A
  exact congrArg (fun k => k.hom.app A) h

end IntConstruction
end CategoryTheory
