/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.StupidTruncInvNaturality
public import MathlibExt.Algebra.Homology.PartialTotalNested

/-!
# Coordinates of partial totals

The coordinate inclusions identify retained bicomplex cells with
summands of a partial total and characterize maps on those summands.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The canonical coordinate inclusion of a retained bicomplex cell into a
partial total.  Its codomain is the public `partialTotal`, so clients do not
need to unfold the semireducible `firstStupidTrunc`/`partialTotal` definitions. -/
noncomputable def partialTotalComponent (p : ℕ) (i : Fin (p + 1))
    (j n : ℕ) (hn : i.1 + j = n) :
    (B.X i.1).X j ⟶ (B.partialTotal p).X n := by
  let e := ComplexShape.embeddingDownNatInitialSegment p
  have hi : e.f i = i.1 := by
    change (i : ℕ) = i
    rfl
  let hST : B.stupidTrunc e = B.firstStupidTrunc p := rfl
  let hPT : (B.firstStupidTrunc p).total (ComplexShape.down ℕ) =
      B.partialTotal p := rfl
  exact (B.stupidTruncXIso e hi).inv.f j ≫
    eqToHom (congrArg (fun K => (K.X i.1).X j) hST) ≫
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) i.1 j n hn ≫
    eqToHom (congrArg (fun K => K.X n) hPT)

set_option backward.isDefEq.respectTransparency false

/-- The partial-total cell coordinates are natural in bicomplex morphisms. -/
@[reassoc]
theorem partialTotalComponent_naturality
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)}
    (φ : B ⟶ B') (p : ℕ) (i : Fin (p + 1))
    (j n : ℕ) (hn : i.1 + j = n) :
    B.partialTotalComponent p i j n hn ≫ (B.partialTotalHom φ p).f n =
      (φ.f i.1).f j ≫ B'.partialTotalComponent p i j n hn := by
  let e := ComplexShape.embeddingDownNatInitialSegment p
  have hi : e.f i = i.1 := by
    change (i : ℕ) = i
    rfl
  let hST : B.stupidTrunc e = B.firstStupidTrunc p := rfl
  let hST' : B'.stupidTrunc e = B'.firstStupidTrunc p := rfl
  let hPT : (B.firstStupidTrunc p).total (ComplexShape.down ℕ) =
      B.partialTotal p := rfl
  let hPT' : (B'.firstStupidTrunc p).total (ComplexShape.down ℕ) =
      B'.partialTotal p := rfl
  let inc : ((B.stupidTrunc e).X i.1).X j ⟶ (B.partialTotal p).X n :=
    eqToHom (congrArg (fun K => (K.X i.1).X j) hST) ≫
      (B.firstStupidTrunc p).ιTotal
        (ComplexShape.down ℕ) i.1 j n hn ≫
      eqToHom (congrArg (fun K => K.X n) hPT)
  let inc' : ((B'.stupidTrunc e).X i.1).X j ⟶ (B'.partialTotal p).X n :=
    eqToHom (congrArg (fun K => (K.X i.1).X j) hST') ≫
      (B'.firstStupidTrunc p).ιTotal
        (ComplexShape.down ℕ) i.1 j n hn ≫
      eqToHom (congrArg (fun K => K.X n) hPT')
  have hcoord : B.partialTotalComponent p i j n hn =
      (B.stupidTruncXIso e hi).inv.f j ≫ inc := by
    rfl
  have hcoord' : B'.partialTotalComponent p i j n hn =
      (B'.stupidTruncXIso e hi).inv.f j ≫ inc' := by
    rfl
  rw [hcoord, hcoord']
  have hι := B.ιTotal_partialTotalHom φ p i j n hn
  have hinc : inc ≫ (B.partialTotalHom φ p).f n =
      ((HomologicalComplex.stupidTruncMap φ e).f i.1).f j ≫ inc' := by
    dsimp only [inc, inc', hST, hST', hPT, hPT']
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hι
  have htrunc := HomologicalComplex.stupidTruncXIso_inv_naturality
    e φ hi
  have htruncj := HomologicalComplex.congr_hom htrunc j
  simp only [HomologicalComplex.comp_f] at htruncj
  simp only [Category.assoc]
  rw [hinc, ← Category.assoc, ← htruncj, Category.assoc]


/-- A retained cell coordinate followed by the partial-total inclusion is the
corresponding full-total generator. -/
@[reassoc]
theorem partialTotalComponent_comp_partialTotalι
    (p : ℕ) (i : Fin (p + 1)) (j n : ℕ) (hn : i.1 + j = n) :
    B.partialTotalComponent p i j n hn ≫ (B.partialTotalι p).f n =
      B.ιTotal (ComplexShape.down ℕ) i.1 j n hn := by
  let e := ComplexShape.embeddingDownNatInitialSegment p
  have hi : e.f i = i.1 := by
    change (i : ℕ) = i
    rfl
  let hST : B.stupidTrunc e = B.firstStupidTrunc p := rfl
  let hPT : (B.firstStupidTrunc p).total (ComplexShape.down ℕ) =
      B.partialTotal p := rfl
  let inc : ((B.stupidTrunc e).X i.1).X j ⟶ (B.partialTotal p).X n :=
    eqToHom (congrArg (fun K => (K.X i.1).X j) hST) ≫
      (B.firstStupidTrunc p).ιTotal
        (ComplexShape.down ℕ) i.1 j n hn ≫
      eqToHom (congrArg (fun K => K.X n) hPT)
  have hcoord : B.partialTotalComponent p i j n hn =
      (B.stupidTruncXIso e hi).inv.f j ≫ inc := by
    rfl
  rw [hcoord]
  have hι := B.ιTotal_partialTotalι p i j n hn
  have hinc : inc ≫ (B.partialTotalι p).f n =
      (B.stupidTruncXIso e hi).hom.f j ≫
        B.ιTotal (ComplexShape.down ℕ) i.1 j n hn := by
    dsimp only [inc, hST, hPT]
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hι
  simp only [Category.assoc, hinc]
  have hid := HomologicalComplex.congr_hom
    (Iso.inv_hom_id (B.stupidTruncXIso e hi)) j
  have hId : ((𝟙 (B.X i.1) : B.X i.1 ⟶ B.X i.1).f j) = 𝟙 _ := rfl
  simpa only [HomologicalComplex.comp_f, Category.assoc, hId,
    Category.id_comp] using congrArg
      (fun k => k ≫ B.ιTotal (ComplexShape.down ℕ) i.1 j n hn) hid


/-- Retained-cell coordinates commute with inclusions between partial-total
filtration stages. -/
@[reassoc]
theorem partialTotalComponent_partialTotalMap
    {p p' : ℕ} (h : p ≤ p') (i : Fin (p + 1))
    (j n : ℕ) (hn : i.1 + j = n) :
    B.partialTotalComponent p i j n hn ≫ (B.partialTotalMap h).f n =
      B.partialTotalComponent p' ⟨i.1, by omega⟩ j n hn := by
  apply (cancel_mono ((B.partialTotalι p').f n)).1
  have hmap := HomologicalComplex.congr_hom
    (B.partialTotalMap_comp_partialTotalι h) n
  simp only [HomologicalComplex.comp_f] at hmap
  simp only [Category.assoc, B.partialTotalComponent_comp_partialTotalι]
  rw [hmap, B.partialTotalComponent_comp_partialTotalι]



/-- Morphisms out of a partial total are determined by their composites with
all retained-cell coordinates. -/
theorem partialTotal_hom_ext (p : ℕ) {L : ChainComplex C ℕ}
    {f g : B.partialTotal p ⟶ L}
    (h : ∀ (i : Fin (p + 1)) (j n : ℕ) (hn : i.1 + j = n),
      B.partialTotalComponent p i j n hn ≫ f.f n =
        B.partialTotalComponent p i j n hn ≫ g.f n) :
    f = g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  by_cases hi : i < p + 1
  · let i' : Fin (p + 1) := ⟨i, hi⟩
    let e := ComplexShape.embeddingDownNatInitialSegment p
    have hi' : e.f i' = i := by
      change (i : ℕ) = i
      rfl
    apply (cancel_epi ((B.stupidTruncXIso e hi').inv.f j)).1
    have hc := h i' j n hij
    unfold partialTotalComponent at hc
    dsimp only at hc
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
      Category.assoc] using hc
  · have hz : IsZero (((B.firstStupidTrunc p).X i).X j) := by
      apply (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero
      apply B.isZero_stupidTrunc_X
        (ComplexShape.embeddingDownNatInitialSegment p)
      intro a ha
      change a.1 = i at ha
      omega
    exact hz.eq_of_src _ _

/-- The stagewise partial-total map induced by an identity bicomplex map is
the identity. -/
@[simp]
theorem partialTotalHom_id (p : ℕ) :
    B.partialTotalHom (𝟙 B) p = 𝟙 (B.partialTotal p) := by
  apply B.partialTotal_hom_ext p
  intro i j n hn
  simpa only [HomologicalComplex.id_f, Category.id_comp, Category.comp_id] using
    B.partialTotalComponent_naturality (𝟙 B) p i j n hn

/-- Stagewise partial-total maps compose with the underlying bicomplex maps. -/
@[reassoc]
theorem partialTotalHom_comp
    {B' B'' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)}
    (φ : B ⟶ B') (ψ : B' ⟶ B'') (p : ℕ) :
    B.partialTotalHom (φ ≫ ψ) p =
      B.partialTotalHom φ p ≫ B'.partialTotalHom ψ p := by
  apply B.partialTotal_hom_ext p
  intro i j n hn
  calc
    B.partialTotalComponent p i j n hn ≫
          (B.partialTotalHom (φ ≫ ψ) p).f n =
        ((φ.f i.1).f j ≫ (ψ.f i.1).f j) ≫
          B''.partialTotalComponent p i j n hn := by
      rw [B.partialTotalComponent_naturality]
      rfl
    _ = (φ.f i.1).f j ≫
        ((ψ.f i.1).f j ≫ B''.partialTotalComponent p i j n hn) :=
      Category.assoc _ _ _
    _ = (φ.f i.1).f j ≫
        (B'.partialTotalComponent p i j n hn ≫
          (B'.partialTotalHom ψ p).f n) := by
      rw [B'.partialTotalComponent_naturality]
    _ = ((φ.f i.1).f j ≫ B'.partialTotalComponent p i j n hn) ≫
        (B'.partialTotalHom ψ p).f n :=
      (Category.assoc _ _ _).symm
    _ = (B.partialTotalComponent p i j n hn ≫
          (B.partialTotalHom φ p).f n) ≫
        (B'.partialTotalHom ψ p).f n := by
      rw [B.partialTotalComponent_naturality]
    _ = B.partialTotalComponent p i j n hn ≫
        ((B.partialTotalHom φ p).f n ≫
          (B'.partialTotalHom ψ p).f n) :=
      Category.assoc _ _ _



end HomologicalComplex₂
