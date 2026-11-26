/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalTwoColumnZeroEdge

/-!
# Two-column partial-total homology and its canonical edge sequence

Let B be a first-quadrant bicomplex in an abelian category and E its increasing homological
partial-total spectral sequence, with d_r of bidegree (-r,r−1). Assume its second page is
supported in columns zero and one: E^2_{p,q}=0 for every p≥2. For p≤1, the surviving second-page
object identifies with the stable interval S_{p+q,p}=E_Y(⊥,p−1,p,⊤;−(p+q)) of the partial-total
spectral object Y. Here p−1 is an integer cut.

In total degree n=q+1 with q∈ℕ, the image filtration F_0⊂F_1⊂H_n(Tot B) has F_1≅H_n(Tot B), and
its two adjacent graded pieces identify with E^2_{0,q+1} and E^2_{1,q}. The zero-column edge is
the map through S_{n,0} and F_0 into total homology. The right edge is the quotient by F_0 after
identifying total homology with F_1. These arrows give the canonical short exact sequence
0→E^2_{0,q+1}→H_{q+1}(Tot B)→E^2_{1,q}→0 in arbitrary category universes.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

local notation "E" =>
  B.partialTotalSpectralObject.spectralSequence core

/-- Let C be abelian and B a bicomplex of shape (down ℕ,down ℕ). Write E^r_{p,q} for its increasing
homological partial-total spectral sequence, and assume E^2_{p,q}=0 for every p≥2 and q∈ℕ. For
p,q∈ℕ with p≤1 and n=p+q, let S_{n,p}=E_Y(⊥,p−1,p,⊤;−n) be the stable interval of the
partial-total spectral object Y. This canonical isomorphism E^2_{p,q}≅S_{n,p} follows the
spectral-object survivor coordinate from page two to page n+2 and then the stable-page
comparison. The cut p−1 is interpreted in ℤ, including -1 at p=0. -/
noncomputable def partialTotalTwoColumnPageTwoStableIso
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (p q : ℕ) (hp : p ≤ 1) :
    B.partialTotalFirstPageChoice.pageTwo.X (p, q) ≅ B.partialTotalStableObj (p + q) p :=
  B.partialTotalTwoColumnPageTwoToPageIso h₂ (p + q) p q hp ≪≫
    (E).pageXIsoOfEq (p, q) (((2 + (p + q) : ℕ) : ℤ))
      (((p + q + 2 : ℕ) : ℤ)) (by omega) ≪≫
    B.partialTotalStablePageIso p q

private noncomputable def partialTotalTwoColumnZeroColumnPageTwoStableIso
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    B.partialTotalFirstPageChoice.pageTwo.X (0, q) ≅ B.partialTotalStableObj q 0 :=
  B.partialTotalTwoColumnPageTwoToPageIso h₂ q 0 q (Nat.zero_le 1) ≪≫
    (show ((E).page (((2 + q : ℕ) : ℤ))).X (0, q) ≅
        ((E).page (((q + 2 : ℕ) : ℤ))).X (0, q) from
      (E).pageXIsoOfEq (0, q) (((2 + q : ℕ) : ℤ))
        (((q + 2 : ℕ) : ℤ))
        (congrArg (fun n : ℕ => (n : ℤ)) (Nat.add_comm 2 q))) ≪≫
    (show ((E).page (((q + 2 : ℕ) : ℤ))).X (0, q) ≅
        B.partialTotalStableObj q 0 from
      (E).pageXIsoOfEq (0, q) (((q + 2 : ℕ) : ℤ))
          (((0 + q + 2 : ℕ) : ℤ))
          (congrArg (fun n : ℕ => (n : ℤ))
            (congrArg (fun m : ℕ => m + 2) (Nat.zero_add q).symm)) ≪≫
        B.partialTotalStablePageIso 0 q ≪≫
        eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
          (Nat.zero_add q)))

private noncomputable def partialTotalTwoColumnZeroIndexIso (q : ℕ) :
    (B.partialTotalHomologyFiltration (q + 1)).obj
        (((0 : ℤ) : EInt)) ≅
      (B.partialTotalHomologyGradedShortComplex (q + 1) 1).X₁ := by
  let F := B.partialTotalHomologyFiltration (q + 1)
  have hzero : (((0 : ℤ) : EInt)) =
      partialTotalHomologyPreviousIndex 1 := by
    simp only [partialTotalHomologyPreviousIndex_succ, Nat.cast_zero]
  exact eqToIso (congrArg F.obj hzero)

local notation "zeroIndexIso" => partialTotalTwoColumnZeroIndexIso

private theorem partialTotalTwoColumnZeroIndexIso_hom_comp_ι (q : ℕ) :
    (zeroIndexIso B q).hom ≫
        (B.partialTotalHomologyFiltration (q + 1)).ι.app
          (partialTotalHomologyPreviousIndex 1) =
      (B.partialTotalHomologyFiltration (q + 1)).ι.app
        (((0 : ℤ) : EInt)) := by
  let F := B.partialTotalHomologyFiltration (q + 1)
  have hzero : (((0 : ℤ) : EInt)) =
      partialTotalHomologyPreviousIndex 1 := by
    simp only [partialTotalHomologyPreviousIndex_succ, Nat.cast_zero]
  dsimp only [partialTotalTwoColumnZeroIndexIso]
  change eqToHom (congrArg F.diagram.obj hzero) ≫
    F.ι.app (partialTotalHomologyPreviousIndex 1) =
      F.ι.app (((0 : ℤ) : EInt))
  rw [← CategoryTheory.eqToHom_map F.diagram hzero]
  exact (F.ι.naturality (eqToHom hzero)).trans (Category.comp_id _)

local notation "zeroIndexIso_hom_comp_ι" =>
  partialTotalTwoColumnZeroIndexIso_hom_comp_ι

private theorem partialTotalZeroColumnPageToStable_eq_twoColumnStableIso
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    B.partialTotalZeroColumnPageToStable q =
      (B.partialTotalTwoColumnZeroColumnPageTwoStableIso h₂ q).hom := by
  unfold partialTotalTwoColumnZeroColumnPageTwoStableIso
  exact B.partialTotalZeroColumnPageToStable_eq_pageTwoToStable_of_twoColumn h₂ q

/-- Let C be abelian and B a bicomplex of shape (down ℕ,down ℕ). Write E^r_{p,q} for its increasing
homological partial-total spectral sequence, and assume E^2_{p,q}=0 for every p≥2 and q∈ℕ. For
q∈ℕ, the specified zero-column map θ_q:E^2_{0,q}→S_{q,0}, where S_{q,0}=E_Y(⊥,-1,0,⊤;−q), is an
isomorphism. The map θ_q is the chosen page-two coordinate followed by its source-presentation
identification and the stable-tail map; the conclusion applies to that arrow. -/
theorem isIso_partialTotalZeroColumnPageToStable_of_twoColumn
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) : IsIso (B.partialTotalZeroColumnPageToStable q) := by
  rw [B.partialTotalZeroColumnPageToStable_eq_twoColumnStableIso h₂ q]
  infer_instance

private theorem isZero_partialTotalHomologyGradedPiece_of_twoColumn
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (n p : ℕ) (hp : 2 ≤ p) (hpn : p ≤ n) :
    IsZero (B.partialTotalHomologyGradedPiece n p) := by
  let q := n - p
  have hn : p + q = n := Nat.add_sub_of_le hpn
  have hPage : IsZero
      (((E).page (((p + q + 2 : ℕ) : ℤ))).X (p, q)) := by
    exact IsZero.of_iso
      (h₂.isZero_page_two_add_X (p + q) p q hp)
      ((E).pageXIsoOfEq (p, q) (((p + q + 2 : ℕ) : ℤ))
        (((2 + (p + q) : ℕ) : ℤ)) (by omega))
  have hStable : IsZero (B.partialTotalStableObj (p + q) p) :=
    IsZero.of_iso hPage (B.partialTotalStablePageIso p q).symm
  have hStable' : IsZero (B.partialTotalStableObj n p) := by
    simpa only [hn] using hStable
  exact IsZero.of_iso hStable'
    (B.partialTotalStableGradedIso n p).symm

private theorem isIso_partialTotalHomologyFiltrationAdjacentHom_of_twoColumn
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (n p : ℕ) (hp : 2 ≤ p) (hpn : p ≤ n) :
    IsIso (B.partialTotalHomologyFiltrationAdjacentHom n p) := by
  apply (B.partialTotalHomologyGradedShortComplex_shortExact n p).isIso_f_iff.mpr
  exact B.isZero_partialTotalHomologyGradedPiece_of_twoColumn h₂ n p hp hpn

private theorem isIso_partialTotalHomologyFiltration_map_one_to_of_twoColumn
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    IsIso ((B.partialTotalHomologyFiltration n).diagram.map
      (homOfLE (show (((1 : ℕ) : ℤ) : EInt) ≤
        ((((k + 1 : ℕ) : ℤ) : EInt)) by
          simp only [WithBotTop.coe_le_coe]
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)))) := by
  induction k with
  | zero =>
      rw [Subsingleton.elim
        (homOfLE (show (((1 : ℕ) : ℤ) : EInt) ≤
          ((((0 + 1 : ℕ) : ℤ) : EInt)) by simp))
        (𝟙 (((1 : ℕ) : ℤ) : EInt))]
      infer_instance
  | succ k ih =>
      have hk' : k + 1 ≤ n := by omega
      let f := (B.partialTotalHomologyFiltration n).diagram.map
        (homOfLE (show (((1 : ℕ) : ℤ) : EInt) ≤
          ((((k + 1 : ℕ) : ℤ) : EInt)) by
            simp only [WithBotTop.coe_le_coe]
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)))
      let g := B.partialTotalHomologyFiltrationAdjacentHom n (k + 2)
      have hcomp :
          (B.partialTotalHomologyFiltration n).diagram.map
              (homOfLE (show (((1 : ℕ) : ℤ) : EInt) ≤
                ((((k + 2 : ℕ) : ℤ) : EInt)) by
                  simp only [WithBotTop.coe_le_coe]
                  exact_mod_cast Nat.succ_le_succ (Nat.zero_le (k + 1)))) =
            f ≫ g := by
        dsimp only [f, g]
        rw [B.partialTotalHomologyFiltrationAdjacentHom_succ]
        rw [← Functor.map_comp]
        apply (B.partialTotalHomologyFiltration n).diagram.congr_map
        subsingleton
      rw [hcomp]
      exact IsIso.comp_isIso' (ih hk')
        (B.isIso_partialTotalHomologyFiltrationAdjacentHom_of_twoColumn
          h₂ n (k + 2) (by omega) (by omega))

/-- Let C be abelian and B a bicomplex of shape (down ℕ,down ℕ). Write E^r_{p,q} for its increasing
homological partial-total spectral sequence, and assume E^2_{p,q}=0 for every p≥2 and q∈ℕ. For
q∈ℕ and n=q+1, let F_pH_n(Tot B)=image(H_n(P_p(B))→H_n(Tot B)) be the partial-total image
filtration. The inclusion ι_1:F_1H_n(Tot B)→H_n(Tot B) is an isomorphism. All higher adjacent
graded pieces vanish under the two-column hypothesis, and the finite filtration is exhaustive at
stage n. -/
theorem isIso_partialTotalHomologyFiltration_ι_app_one_of_twoColumn
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    IsIso ((B.partialTotalHomologyFiltration (q + 1)).ι.app
      (((1 : ℕ) : ℤ) : EInt)) := by
  let F := B.partialTotalHomologyFiltration (q + 1)
  let f := F.diagram.map
    (homOfLE (show (((1 : ℕ) : ℤ) : EInt) ≤
      ((((q + 1 : ℕ) : ℤ) : EInt)) by
        simp only [WithBotTop.coe_le_coe]
        exact_mod_cast Nat.le_add_left 1 q))
  let g := F.ι.app ((((q + 1 : ℕ) : ℤ) : EInt))
  let _ : IsIso f :=
    B.isIso_partialTotalHomologyFiltration_map_one_to_of_twoColumn h₂
      (q + 1) q (by omega)
  let _ : IsIso g :=
    B.partialTotalHomologyFiltration_exhaustive_at_degree (q + 1)
  have hfg : f ≫ g = F.ι.app (((1 : ℕ) : ℤ) : EInt) :=
    B.partialTotalHomologyFiltration_map_comp_ι (q + 1) (by
      simp only [WithBotTop.coe_le_coe]
      exact_mod_cast Nat.le_add_left 1 q)
  rw [← hfg]
  infer_instance

/-- Let C be abelian and B a bicomplex of shape (down ℕ,down ℕ). Write E^r_{p,q} for its increasing
homological partial-total spectral sequence, and assume E^2_{p,q}=0 for every p≥2 and q∈ℕ. For
q∈ℕ set n=q+1, let ι_1:F_1H_n(Tot B)≅H_n(Tot B) be the stage-one inclusion and π_1:F_1H_n(Tot
B)→gr_1H_n(Tot B) its quotient by F_0. Write u:S_{n,1}≅gr_1H_n(Tot B) for the stable-graded
comparison and e:E^2_{1,q}≅S_{n,1} for the two-column survivor comparison. This right edge
H_n(Tot B)→E^2_{1,q} is ι_1^{-1}≫π_1≫u.inv≫e.inv. -/
noncomputable def partialTotalOneColumnRightEdge
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    (B.total (ComplexShape.down ℕ)).homology (q + 1) ⟶
      B.partialTotalFirstPageChoice.pageTwo.X (1, q) := by
  let f := (B.partialTotalHomologyFiltration (q + 1)).ι.app
    (((1 : ℕ) : ℤ) : EInt)
  let _ : IsIso f :=
    B.isIso_partialTotalHomologyFiltration_ι_app_one_of_twoColumn h₂ q
  let e : ((E).page (2 : ℤ)).X (1, q) ≅
      B.partialTotalStableObj (q + 1) 1 := by
    simpa only [Nat.add_comm] using
      B.partialTotalTwoColumnPageTwoStableIso h₂ 1 q (by omega)
  exact inv f ≫
    B.partialTotalHomologyGradedπ (q + 1) 1 ≫
    (B.partialTotalStableGradedIso (q + 1) 1).inv ≫
    e.inv

private noncomputable def partialTotalTwoColumnZeroColumnFiltrationIso
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    B.partialTotalFirstPageChoice.pageTwo.X (0, q + 1) ≅
      (B.partialTotalHomologyGradedShortComplex (q + 1) 1).X₁ := by
  exact (B.partialTotalTwoColumnZeroColumnPageTwoStableIso h₂ (q + 1) ≪≫
      B.partialTotalStableGradedIso (q + 1) 0 ≪≫
      (B.partialTotalHomologyGradedZeroIso (q + 1)).symm) ≪≫
    zeroIndexIso B q

private noncomputable def partialTotalTwoColumnOneColumnGradedIso
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    B.partialTotalFirstPageChoice.pageTwo.X (1, q) ≅
      (B.partialTotalHomologyGradedShortComplex (q + 1) 1).X₃ := by
  change ((E).page (2 : ℤ)).X (1, q) ≅
    B.partialTotalHomologyGradedPiece (q + 1) 1
  let e : ((E).page (2 : ℤ)).X (1, q) ≅
      B.partialTotalStableObj (q + 1) 1 := by
    simpa only [Nat.add_comm] using
      B.partialTotalTwoColumnPageTwoStableIso h₂ 1 q (by omega)
  exact e ≪≫
    B.partialTotalStableGradedIso (q + 1) 1

private noncomputable def partialTotalTwoColumnTotalFiltrationOneIso
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    (B.total (ComplexShape.down ℕ)).homology (q + 1) ≅
      (B.partialTotalHomologyGradedShortComplex (q + 1) 1).X₂ := by
  change (B.total (ComplexShape.down ℕ)).homology (q + 1) ≅
    (B.partialTotalHomologyFiltration (q + 1)).obj
      (((1 : ℕ) : ℤ) : EInt)
  let f := (B.partialTotalHomologyFiltration (q + 1)).ι.app
    (((1 : ℕ) : ℤ) : EInt)
  let _ : IsIso f :=
    B.isIso_partialTotalHomologyFiltration_ι_app_one_of_twoColumn h₂ q
  exact (asIso f).symm

/-- Let C be abelian and B a bicomplex of shape (down ℕ,down ℕ). Write E^r_{p,q} for its increasing
homological partial-total spectral sequence, and assume E^2_{p,q}=0 for every p≥2 and q∈ℕ. For
q∈ℕ, this short complex is E^2_{0,q+1}→H_{q+1}(Tot B)→E^2_{1,q}. The first arrow is the
zero-column edge through its stable interval and the stage-zero image filtration. The second
identifies total homology with stage one and then takes the adjacent quotient, followed by the
inverse stable-column comparison. The composite is zero because the stage-zero image is killed
by the stage-one quotient. -/
noncomputable abbrev partialTotalTwoColumnShortComplex
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) : ShortComplex C :=
  ShortComplex.mk
    (B.partialTotalZeroColumnEdge (q + 1))
    (B.partialTotalOneColumnRightEdge h₂ q)
    (by
      let F := B.partialTotalHomologyFiltration (q + 1)
      let i₀ := F.ι.app (((0 : ℤ) : EInt))
      let i₁ := F.ι.app
        (((1 : ℕ) : ℤ) : EInt)
      have hzero : (((0 : ℤ) : EInt)) =
          partialTotalHomologyPreviousIndex 1 := by
        simp only [partialTotalHomologyPreviousIndex_succ, Nat.cast_zero]
      let e₀ : F.obj (((0 : ℤ) : EInt)) ≅
          F.obj (partialTotalHomologyPreviousIndex 1) :=
        eqToIso (congrArg F.obj hzero)
      let a := e₀.hom ≫
        B.partialTotalHomologyFiltrationAdjacentHom (q + 1) 1
      let _ : IsIso i₁ :=
        B.isIso_partialTotalHomologyFiltration_ι_app_one_of_twoColumn h₂ q
      have he₀ : e₀.hom ≫
          F.ι.app (partialTotalHomologyPreviousIndex 1) = i₀ := by
        dsimp only [e₀, i₀]
        change eqToHom (congrArg F.diagram.obj hzero) ≫
          F.ι.app (partialTotalHomologyPreviousIndex 1) =
            F.ι.app (((0 : ℤ) : EInt))
        rw [← CategoryTheory.eqToHom_map F.diagram hzero]
        exact (F.ι.naturality (eqToHom hzero)).trans
          (Category.comp_id _)
      have hi : i₀ ≫ inv i₁ = a := by
        rw [← cancel_mono i₁, Category.assoc, IsIso.inv_hom_id,
          Category.comp_id]
        dsimp only [a]
        rw [Category.assoc,
          B.partialTotalHomologyFiltrationAdjacentHom_comp_ι, he₀]
      unfold partialTotalZeroColumnEdge partialTotalOneColumnRightEdge
      rw [B.partialTotalZeroColumnPageToStable_eq_twoColumnStableIso h₂ (q + 1)]
      dsimp only
      simp only [Category.assoc]
      slice_lhs 4 6 => rw [← Category.assoc, hi]
      dsimp only [a]
      slice_lhs 5 7 =>
        rw [← Category.assoc, cokernel.condition, zero_comp]
      simp only [comp_zero, zero_comp])

private noncomputable def partialTotalTwoColumnShortComplexIsoGraded
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    B.partialTotalTwoColumnShortComplex h₂ q ≅
      B.partialTotalHomologyGradedShortComplex (q + 1) 1 := by
  let e₁ := B.partialTotalTwoColumnZeroColumnFiltrationIso h₂ q
  let e₂ := B.partialTotalTwoColumnTotalFiltrationOneIso h₂ q
  let e₃ := B.partialTotalTwoColumnOneColumnGradedIso h₂ q
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · let F := B.partialTotalHomologyFiltration (q + 1)
    let i₀ := F.ι.app (((0 : ℤ) : EInt))
    let i₁ := F.ι.app (((1 : ℕ) : ℤ) : EInt)
    let _ : IsIso i₁ :=
      B.isIso_partialTotalHomologyFiltration_ι_app_one_of_twoColumn h₂ q
    have he₀ : (zeroIndexIso B q).hom ≫
        F.ι.app (partialTotalHomologyPreviousIndex 1) = i₀ := by
      exact zeroIndexIso_hom_comp_ι B q
    have htail : (zeroIndexIso B q).hom ≫
        B.partialTotalHomologyFiltrationAdjacentHom (q + 1) 1 =
          i₀ ≫ inv i₁ := by
      rw [← cancel_mono i₁, Category.assoc,
        B.partialTotalHomologyFiltrationAdjacentHom_comp_ι, he₀]
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hc := congrArg
      (fun z =>
        ((B.partialTotalTwoColumnZeroColumnPageTwoStableIso h₂ (q + 1)).hom ≫
          (B.partialTotalStableGradedIso (q + 1) 0).hom ≫
          (B.partialTotalHomologyGradedZeroIso (q + 1)).inv) ≫ z)
      htail
    dsimp only [e₁, e₂, partialTotalTwoColumnShortComplex,
      partialTotalTwoColumnZeroColumnFiltrationIso,
      partialTotalTwoColumnTotalFiltrationOneIso,
      partialTotalZeroColumnEdge]
    rw [B.partialTotalZeroColumnPageToStable_eq_twoColumnStableIso h₂ (q + 1)]
    simpa only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
      id, i₀, i₁, F] using hc
  · let i₁ := (B.partialTotalHomologyFiltration (q + 1)).ι.app
      (((1 : ℕ) : ℤ) : EInt)
    let _ : IsIso i₁ :=
      B.isIso_partialTotalHomologyFiltration_ι_app_one_of_twoColumn h₂ q
    dsimp only [e₂, e₃, partialTotalTwoColumnShortComplex,
      partialTotalTwoColumnTotalFiltrationOneIso,
      partialTotalTwoColumnOneColumnGradedIso,
      partialTotalOneColumnRightEdge]
    dsimp only [id]
    simp only [Iso.symm_hom, asIso_inv, Iso.trans_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Let C be abelian and B a bicomplex of shape (down ℕ,down ℕ). Write E^r_{p,q} for its increasing
homological partial-total spectral sequence, and assume E^2_{p,q}=0 for every p≥2 and q∈ℕ. For
every q∈ℕ, the specified edge arrows give a short exact sequence 0→E^2_{0,q+1}→H_{q+1}(Tot
B)→E^2_{1,q}→0. It is the adjacent image-filtration sequence 0→F_0→F_1→gr_1→0 transported
through the survivor and stable-graded isomorphisms and the canonical isomorphism
F_1≅H_{q+1}(Tot B). -/
theorem partialTotalTwoColumnShortComplex_shortExact
    (h₂ : CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E)
    (q : ℕ) :
    (B.partialTotalTwoColumnShortComplex h₂ q).ShortExact :=
  ShortComplex.shortExact_of_iso
    (B.partialTotalTwoColumnShortComplexIsoGraded h₂ q).symm
    (B.partialTotalHomologyGradedShortComplex_shortExact (q + 1) 1)

end HomologicalComplex₂

end
