/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RelativePrism
import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexSimplexHomExt
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.LeftHornLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Fibration

/-!
# Whole relative boundary prisms controlled by cocartesian edges

The original source-prism shuffle ladder has one critical initial horn.
Its actual first vertical edge is cocartesian, so the native left-horn
criterion supplies the whole filler over the prescribed base simplex.
All other steps use innerness. Degree zero uses the original cocartesian
base-edge lift. The proof adapts the original relative equivalence-prism
filtration with its actual cocartesian critical edge; no base Kan
hypothesis or localization comparison is used.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite
open scoped Simplicial

namespace SSet

/-- All original vertical edges of this full prism are cocartesian for the supplied map. -/
def PrismOneVerticalsCocartesian {T X B : SSet.{u}} (p : X ⟶ B)
    (F : T ⊗ Δ[1] ⟶ X) : Prop :=
  ∀ x : T _⦋0⦌, CocartesianEdge.IsPCocartesian p
    (yonedaEquiv.symm (F.app _ (verticalOneSimplex x)))

/-- The original boundary prism extends with every whole base simplex and cocartesian vertical unchanged. -/
def RelativeCocartesianPrismSrcExtension {A D X B : SSet.{u}} (i : A ⟶ D) (p : X ⟶ B) : Prop :=
  ∀ (H : A ⊗ Δ[1] ⟶ X) (c : D ⟶ X) (K : D ⊗ Δ[1] ⟶ B),
    prismSectionAt A 0 ≫ H = i ≫ c →
    prismSectionAt D 0 ≫ K = c ≫ p →
    H ≫ p = (i ▷ Δ[1]) ≫ K →
    PrismOneVerticalsCocartesian p H →
      ∃ F : D ⊗ Δ[1] ⟶ X,
        (i ▷ Δ[1]) ≫ F = H ∧ prismSectionAt D 0 ≫ F = c ∧
          F ≫ p = K ∧ PrismOneVerticalsCocartesian p F

private def Edge.IsPCocartesian {X B : SSet.{u}} {x y : X _⦋0⦌}
    (e : Edge x y) (p : X ⟶ B) : Prop :=
  CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm e.edge)

private theorem edgePCocartesian_iff_of_edge_eq {X B : SSet.{u}} (p : X ⟶ B)
    {x y x' y' : X _⦋0⦌} {e : Edge x y} {e' : Edge x' y'} (h : e.edge = e'.edge) :
    e.IsPCocartesian p ↔ e'.IsPCocartesian p := by
  dsimp only [Edge.IsPCocartesian]
  rw [h]

private theorem critical_left_edge (m : ℕ) {X B : SSet.{u}} (p : X ⟶ B)
    {φ : ((prismSrcFilt (m + 1) 1 : (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X}
    {φ₀ : ((prismSrcInitial (m + 1) : (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X}
    (hrestr : Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt 1) ≫ φ = φ₀)
    (hVert : (Edge.mk' (φ₀.app _ ⟨prismVertZero (m + 1),
      prismVertZero_mem_prismSrcInitial (by omega)⟩)).IsPCocartesian p) :
    (leftHornEdge
      (Subcomplex.hornLift (prismSrcFilt (m + 1) 1) (prismTau (m + 1) 0)
        (0 : Fin (m + 2)).castSucc (prismSrcFilt_preimage_prismTauMap (0 : Fin (m + 2))) ≫ φ)).IsPCocartesian p := by
  apply (edgePCocartesian_iff_of_edge_eq p (e := leftHornEdge _)
    (e' := Edge.mk' (φ₀.app _ ⟨prismVertZero (m + 1), prismVertZero_mem_prismSrcInitial (by omega)⟩)) ?_).mpr hVert
  rw [leftHornEdge_hornLift_comp]
  exact congr($(hrestr).app _ ⟨prismVertZero (m + 1), prismVertZero_mem_prismSrcInitial (by omega)⟩)

private lemma exists_relative_extension_prismSrcFilt_of_one_le
    {X Y : SSet.{u}} {p : X ⟶ Y} [InnerFibration p]
    {n : ℕ} (hn : 1 ≤ n)
    (φ₀ : ((prismSrcInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X)
    (K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ Y)
    (hbase₀ : φ₀ ≫ p = (prismSrcInitial n).ι ≫ K)
    (hVert : (Edge.mk' (φ₀.app _ ⟨prismVertZero n,
        prismVertZero_mem_prismSrcInitial hn⟩)).IsPCocartesian p) :
    ∀ (d m : ℕ), m + d = n + 1 →
      ∃ φm : ((prismSrcFilt n m :
          (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X,
        Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt m) ≫ φm = φ₀ ∧
          φm ≫ p = (prismSrcFilt n m).ι ≫ K := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hmn1 : m = n + 1 := by omega
    subst hmn1
    let e : ((prismSrcFilt n (n + 1) :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
        (prismSrcInitial n : SSet.{u}) :=
      Subcomplex.eqToIso prismSrcFilt_top
    refine ⟨e.hom ≫ φ₀, ?_, ?_⟩
    · have hid : Subcomplex.homOfLE
          (prismSrcInitial_le_prismSrcFilt (n + 1)) ≫ e.hom = 𝟙 _ := by
        dsimp only [e]
        rw [Subcomplex.eqToIso_hom, ← cancel_mono (prismSrcInitial n).ι]
        simp
      rw [← Category.assoc, hid, Category.id_comp]
    · rw [Category.assoc, hbase₀]
      change (e.hom ≫ (prismSrcInitial n).ι) ≫ K =
        (prismSrcFilt n (n + 1)).ι ≫ K
      congr 1
  | succ d ih =>
    intro m hm
    have hm1 : (m + 1) + d = n + 1 := by omega
    obtain ⟨φ₁, hφ₁, hφ₁base⟩ := ih (m + 1) hm1
    have hmn : m ≤ n := by omega
    let k : Fin (n + 1) := ⟨m, by omega⟩
    have hpreK : (prismSrcFilt n (k.val + 1)).preimage
        (yonedaEquiv.symm (prismTau n k)) = Λ[n + 1, k.castSucc] :=
      prismSrcFilt_preimage_prismTauMap.{u} k
    have hpre : (prismSrcFilt n (m + 1)).preimage
        (yonedaEquiv.symm (prismTau n k)) = Λ[n + 1, k.castSucc] := by
      simpa only [k] using hpreK
    let σY : (Δ[n + 1] : SSet.{u}) ⟶ Y :=
      yonedaEquiv.symm (K.app _ (prismTau n k))
    have hsq :
        (Subcomplex.hornLift (prismSrcFilt n (m + 1))
            (prismTau n k) k.castSucc hpre ≫ φ₁) ≫ p =
          Λ[n + 1, k.castSucc].ι ≫ σY := by
      rw [Category.assoc, hφ₁base]
      change ((Subcomplex.hornLift (prismSrcFilt n (m + 1))
          (prismTau n k) k.castSucc hpre ≫
            (prismSrcFilt n (m + 1)).ι) ≫ K) = _
      rw [Subcomplex.hornLift_ι, Category.assoc,
        yonedaEquiv_symm_comp]
    obtain ⟨σX, hσX, hσXbase⟩ : ∃ σX : (Δ[n + 1] : SSet.{u}) ⟶ X,
        Subcomplex.hornLift (prismSrcFilt n (m + 1))
              (prismTau n k) k.castSucc hpre ≫ φ₁ =
            Λ[n + 1, k.castSucc].ι ≫ σX ∧
          σX ≫ p = σY := by
      by_cases hm0 : m = 0
      · subst hm0
        obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨σX, hσX, hσXbase⟩ :=
          CocartesianEdge.exists_fill_leftHorn_of_isPCocartesian _ σY hsq
            (critical_left_edge m' p hφ₁ hVert)
        exact ⟨σX, hσX.symm, hσXbase⟩
      · have hk0 : (0 : Fin (n + 2)) < k.castSucc := by
          rw [Fin.lt_def, Fin.val_castSucc]
          change 0 < m
          omega
        have hkn : k.castSucc < Fin.last (n + 1) := by
          rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
          change m < n + 1
          omega
        have hlp : HasLiftingProperty Λ[n + 1, k.castSucc].ι p :=
          InnerFibration.mem _ (horn_ι_mem_innerHornInclusions hk0 hkn)
        obtain ⟨σX, hσX, hσXbase⟩ :=
          hlp.sq_hasLift (CommSq.mk hsq)
        exact ⟨σX, hσX.symm, hσXbase⟩
    obtain ⟨φ', hφ'1, hφ'2⟩ :=
      Subcomplex.exists_extension_sup_of_horn_filler hpre
        (fun h ↦ injective_of_mono _ h) φ₁ σX hσX
    have hφ'base : φ' ≫ p =
        (prismSrcFilt n (m + 1) ⊔
          Subcomplex.ofSimplex (prismTau n k)).ι ≫ K := by
      apply Subcomplex.hom_ext_sup_of_simplex
      · simp only [← Category.assoc, hφ'1, hφ₁base,
          Subcomplex.homOfLE_ι]
      · simp only [← Category.assoc, hφ'2, hσXbase,
          Subcomplex.simplexLiftSup_ι]
        dsimp only [σY]
        rw [yonedaEquiv_symm_comp]
    let e : ((prismSrcFilt n m :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
        ((prismSrcFilt n (m + 1) ⊔
          Subcomplex.ofSimplex (prismTau n k) :
            (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) :=
      Subcomplex.eqToIso (prismSrcFilt_eq_succ_sup hmn)
    refine ⟨e.hom ≫ φ', ?_, ?_⟩
    · have hcomp : Subcomplex.homOfLE
          (prismSrcInitial_le_prismSrcFilt m) ≫ e.hom =
        Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt (m + 1)) ≫
          Subcomplex.homOfLE (show prismSrcFilt n (m + 1) ≤
            prismSrcFilt n (m + 1) ⊔
              Subcomplex.ofSimplex (prismTau n k) from
            le_sup_left) := by
        dsimp only [e]
        rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
      rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
      exact hφ₁
    · rw [Category.assoc, hφ'base]
      change (e.hom ≫
          (prismSrcFilt n (m + 1) ⊔
            Subcomplex.ofSimplex (prismTau n k)).ι) ≫ K =
        (prismSrcFilt n m).ι ≫ K
      congr 1

/-- Positive-dimensional relative source-prism cell extension. This is the
cell engine needed for the covering homotopy extension theorem: every attached
simplex retains its complete prescribed image in the base. -/
private theorem exists_relativePrism_extension_boundary_of_one_le
    {X Y : SSet.{u}} {p : X ⟶ Y} [InnerFibration p]
    {n : ℕ} (hn : 1 ≤ n)
    (φ₀ : ((prismSrcInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X)
    (K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ Y)
    (hbase₀ : φ₀ ≫ p = (prismSrcInitial n).ι ≫ K)
    (hVert : (Edge.mk' (φ₀.app _ ⟨prismVertZero n,
        prismVertZero_mem_prismSrcInitial hn⟩)).IsPCocartesian p) :
    ∃ F : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      (prismSrcInitial n).ι ≫ F = φ₀ ∧ F ≫ p = K := by
  obtain ⟨φm, hφm, hφmbase⟩ :=
    exists_relative_extension_prismSrcFilt_of_one_le hn φ₀ K hbase₀ hVert
      (n + 1) 0 (by omega)
  let e : ((prismSrcFilt n 0 :
      (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
      (Δ[n] ⊗ Δ[1] : SSet.{u}) :=
    Subcomplex.eqToIso prismSrcFilt_zero ≪≫ Subcomplex.topIso _
  refine ⟨e.inv ≫ φm, ?_, ?_⟩
  · have hhom : e.hom = (prismSrcFilt n 0).ι := by
      dsimp only [e]
      rw [Iso.trans_hom, Subcomplex.eqToIso_hom,
        Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
    have hι : (prismSrcInitial n).ι =
        Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt 0) ≫ e.hom := by
      rw [hhom]
      exact (Subcomplex.homOfLE_ι _).symm
    rw [hι, Category.assoc, ← Category.assoc e.hom e.inv φm,
      Iso.hom_inv_id, Category.id_comp]
    exact hφm
  · rw [Category.assoc, hφmbase]
    have hhom : e.hom = (prismSrcFilt n 0).ι := by
      dsimp only [e]
      rw [Iso.trans_hom, Subcomplex.eqToIso_hom,
        Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
    rw [← hhom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private lemma prismSectionAt_deltaZero_zero :
    prismSectionAt (Δ[0] : SSet.{u}) (0 : Fin 2) =
      stdSimplex.δ (1 : Fin 2) ≫
        (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv := by
  apply yonedaEquiv.injective
  apply Prod.ext
  · apply yonedaEquiv.symm.injective
    exact stdSimplex.isTerminalObj₀.hom_ext _ _
  · apply stdSimplex.obj₀Equiv.injective
    rfl

private lemma yonedaEquiv_symm_verticalOneSimplex_deltaZero' :
    yonedaEquiv.symm
        (verticalOneSimplex (B := (Δ[0] : SSet.{u}))
          (stdSimplex.obj₀Equiv.symm 0)) =
      (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv := by
  apply CartesianMonoidalCategory.hom_ext
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  · have hleft : yonedaEquiv.symm
          (verticalOneSimplex (B := (Δ[0] : SSet.{u}))
            (stdSimplex.obj₀Equiv.symm 0)) ≫
          CartesianMonoidalCategory.snd _ _ = 𝟙 Δ[1] := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rfl
    have hright : (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫
          CartesianMonoidalCategory.snd _ _ = 𝟙 Δ[1] := rfl
    rw [hleft, hright]

private lemma verticalOneSimplex_deltaZero_eq_yonedaEquiv_leftUnitor_inv :
    verticalOneSimplex (B := (Δ[0] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm 0) =
      yonedaEquiv (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv := by
  apply yonedaEquiv.symm.injective
  rw [yonedaEquiv_symm_verticalOneSimplex_deltaZero',
    Equiv.symm_apply_apply]

private theorem relativeCocartesianPrismSrcExtension_boundary_zero
    {X Y : SSet.{u}} {p : X ⟶ Y} [CocartesianFibration p] :
    RelativeCocartesianPrismSrcExtension ∂Δ[0].ι p := by
  intro H c K _ hKsrc _ _
  let x₀ : X.obj (op (SimplexCategory.mk 0)) := yonedaEquiv c
  let eK : Edge
      (Y.δ 1 (yonedaEquiv
        ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K)))
      (Y.δ 0 (yonedaEquiv
        ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K))) :=
    Edge.mk' (yonedaEquiv
      ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K))
  have hsource : p.app _ x₀ =
      Y.δ 1 (yonedaEquiv
        ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K)) := by
    dsimp only [x₀]
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← yonedaEquiv_comp]
    congr 1
    calc c ≫ p
        = prismSectionAt (Δ[0] : SSet.{u}) 0 ≫ K := hKsrc.symm
      _ = (stdSimplex.δ (1 : Fin 2) ≫
            (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv) ≫ K := by
          rw [prismSectionAt_deltaZero_zero]
      _ = stdSimplex.δ (1 : Fin 2) ≫
            ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K) := by
          rw [Category.assoc]
  let g := eK.ofEq hsource.symm rfl
  obtain ⟨x₁, hx₁, f, hf, hfmap⟩ := CocartesianFibration.lift (p := p) x₀ _ g
  let F : (Δ[0] ⊗ Δ[1] : SSet.{u}) ⟶ X :=
    (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom ≫
      yonedaEquiv.symm f.edge
  have hFbase : F ≫ p = K := by
    rw [← cancel_epi (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv]
    dsimp only [F]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← Edge.map_edge, hfmap]
    rfl
  refine ⟨F, eq_of_boundaryZero_tensor _ _, ?_, hFbase, ?_⟩
  · rw [prismSectionAt_deltaZero_zero]
    dsimp only [F]
    calc
      ((stdSimplex.δ (1 : Fin 2) ≫
          (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv) ≫
            (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom) ≫
          yonedaEquiv.symm f.edge
          = stdSimplex.δ (1 : Fin 2) ≫
              (((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫
                (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom) ≫
                  yonedaEquiv.symm f.edge) := by simp only [Category.assoc]
      _ = stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm f.edge := by
          rw [Iso.inv_hom_id, Category.id_comp]
      _ = yonedaEquiv.symm (X.δ 1 f.edge) := by
          rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      _ = yonedaEquiv.symm x₀ := by rw [f.src_eq]
      _ = c := Equiv.symm_apply_apply yonedaEquiv c
  · intro x
    have hx : x = stdSimplex.obj₀Equiv.symm 0 := by
      apply yonedaEquiv.symm.injective
      exact stdSimplex.isTerminalObj₀.hom_ext _ _
    subst x
    have hval : F.app _
        (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0)) = f.edge := by
      calc F.app _ (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0))
          = yonedaEquiv
              (yonedaEquiv.symm
                (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0)) ≫ F) := by
              rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
        _ = f.edge := by
          rw [yonedaEquiv_symm_verticalOneSimplex_deltaZero']
          dsimp only [F]
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
            Equiv.apply_symm_apply]
    exact hval.symm ▸ hf

private theorem relativeCocartesianPrismSrcExtension_boundary_of_one_le
    {X Y : SSet.{u}} {p : X ⟶ Y} [InnerFibration p]
    {n : ℕ} (hn : 1 ≤ n) :
    RelativeCocartesianPrismSrcExtension ∂Δ[n].ι p := by
  intro H c K hHsrc hKsrc hHK hHvert
  let face0 : (Δ[1] : SSet.{u}).Subcomplex :=
    SSet.stdSimplex.face {0}
  set cface : Δ[n] ⊗ (face0 : SSet.{u}) ⟶ X :=
    CartesianMonoidalCategory.fst _ _ ≫ c with hcface
  have hw : (∂Δ[n].ι ▷ (face0 : SSet.{u})) ≫ cface =
      ((∂Δ[n] : SSet.{u}) ◁ face0.ι) ≫ H := by
    calc (∂Δ[n].ι ▷ (face0 : SSet.{u})) ≫ cface
        = (CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            ∂Δ[n].ι) ≫ c := by
          rw [hcface, ← Category.assoc]
          congr 1
      _ = CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            (prismSectionAt (∂Δ[n] : SSet.{u}) 0 ≫ H) := by
          rw [Category.assoc, ← hHsrc]
      _ = ((∂Δ[n] : SSet.{u}) ◁ face0.ι) ≫ H := by
          dsimp only [face0]
          rw [whiskerLeft_faceZero_ι, Category.assoc]
  let sq := Subcomplex.unionProd.isPushout ∂Δ[n] face0
  let φ₀ := sq.desc cface H hw
  have hι₁ : Subcomplex.unionProd.ι₁ ∂Δ[n] face0 ≫ φ₀ = cface :=
    sq.inl_desc cface H hw
  have hι₂ : Subcomplex.unionProd.ι₂ ∂Δ[n] face0 ≫ φ₀ = H :=
    sq.inr_desc cface H hw
  have hcfaceBase : cface ≫ p = (Δ[n] ◁ face0.ι) ≫ K := by
    calc cface ≫ p
        = CartesianMonoidalCategory.fst Δ[n] (face0 : SSet.{u}) ≫
            (c ≫ p) := by rw [hcface, Category.assoc]
      _ = CartesianMonoidalCategory.fst Δ[n] (face0 : SSet.{u}) ≫
            (prismSectionAt Δ[n] 0 ≫ K) := by rw [hKsrc]
      _ = (Δ[n] ◁ face0.ι) ≫ K := by
          dsimp only [face0]
          rw [whiskerLeft_faceZero_ι, Category.assoc]
  have hι₁ι : Subcomplex.unionProd.ι₁ ∂Δ[n] face0 ≫
        (prismSrcInitial n).ι = Δ[n] ◁ face0.ι := by
    dsimp only [face0, prismSrcInitial]
    exact Subcomplex.unionProd.ι₁_ι ∂Δ[n] (stdSimplex.face {0})
  have hι₂ι : Subcomplex.unionProd.ι₂ ∂Δ[n] face0 ≫
        (prismSrcInitial n).ι = ∂Δ[n].ι ▷ Δ[1] := by
    dsimp only [face0, prismSrcInitial]
    exact Subcomplex.unionProd.ι₂_ι ∂Δ[n] (stdSimplex.face {0})
  have hbase₀ : φ₀ ≫ p =
      (prismSrcInitial n).ι ≫ K := by
    apply sq.hom_ext
    · simp only [← Category.assoc, hι₁, hcfaceBase, hι₁ι]
    · simp only [← Category.assoc, hι₂, hHK, hι₂ι]
  let x0b : (∂Δ[n] : SSet.{u}).obj (op (SimplexCategory.mk 0)) :=
    ⟨stdSimplex.obj₀Equiv.symm 0,
      vertex_mem_boundary_of_one_le hn _⟩
  have happ2 : (Subcomplex.unionProd.ι₂ ∂Δ[n] face0).app _
        (verticalOneSimplex x0b) =
      ⟨prismVertZero n, prismVertZero_mem_prismSrcInitial hn⟩ := by
    apply Subtype.ext
    change (∂Δ[n].ι ▷ Δ[1]).app _ (verticalOneSimplex x0b) =
      prismVertZero n
    have happx : ∂Δ[n].ι.app _ x0b = stdSimplex.obj₀Equiv.symm 0 := rfl
    rw [whiskerRight_app_verticalOneSimplex, happx]
    apply Prod.ext
    · apply stdSimplex.ext
      intro t
      fin_cases t <;> rfl
    · apply stdSimplex.ext
      intro t
      fin_cases t <;> rfl
  have hcriticalEdge : φ₀.app _ ⟨prismVertZero n, prismVertZero_mem_prismSrcInitial hn⟩ =
      H.app _ (verticalOneSimplex x0b) := by
    rw [← happ2]
    exact congr($(hι₂).app _ (verticalOneSimplex x0b))
  have hcritical : CocartesianEdge.IsPCocartesian p
      (yonedaEquiv.symm (φ₀.app _ ⟨prismVertZero n, prismVertZero_mem_prismSrcInitial hn⟩)) :=
    (congrArg (fun e => CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm e)) hcriticalEdge).to_iff.mpr
      (hHvert x0b)
  obtain ⟨F, hF, hFbase⟩ :=
    exists_relativePrism_extension_boundary_of_one_le hn φ₀ K hbase₀ hcritical
  refine ⟨F, ?_, ?_, hFbase, ?_⟩
  · have e₂ : (∂Δ[n].ι ▷ Δ[1]) =
        Subcomplex.unionProd.ι₂ ∂Δ[n] face0 ≫
          (prismSrcInitial n).ι :=
      (Subcomplex.unionProd.ι₂_ι ∂Δ[n] face0).symm
    rw [e₂, Category.assoc, hF, hι₂]
  · apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    have hmemFace : ((prismSectionAt Δ[n] (0 : Fin 2)).app U s).2 ∈
        face0.obj U := by
      subst face0
      change Finset.image
          (stdSimplex.objEquiv
            (((prismSectionAt Δ[n] (0 : Fin 2)).app U s).2)).toOrderHom
            ⊤ ≤ ({0} : Finset (Fin 2))
      rw [Finset.image_subset_iff]
      intro j _
      exact Finset.mem_singleton.2
        (asOrderHom_prismSectionAt_app_snd Δ[n] (0 : Fin 2) s j)
    have hmem : (prismSectionAt Δ[n] 0).app U s ∈
        (prismSrcInitial n).obj U :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl hmemFace)
    let sface : (Δ[n] ⊗ (face0 : SSet.{u})).obj U :=
      (s, ⟨((prismSectionAt Δ[n] 0).app U s).2, hmemFace⟩)
    have happ1 : (Subcomplex.unionProd.ι₁ ∂Δ[n] face0).app U sface =
        ⟨(prismSectionAt Δ[n] 0).app U s, hmem⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact (prismSectionAt_app_fst _ _ s).symm
      · rfl
    change F.app U ((prismSectionAt Δ[n] 0).app U s) = c.app U s
    calc F.app U ((prismSectionAt Δ[n] 0).app U s)
        = φ₀.app U ⟨(prismSectionAt Δ[n] 0).app U s, hmem⟩ :=
          congr($(hF).app U ⟨(prismSectionAt Δ[n] 0).app U s, hmem⟩)
      _ = cface.app U sface := by
          rw [← happ1]
          exact congr($(hι₁).app U sface)
      _ = c.app U s := rfl
  · intro x
    let xb : (∂Δ[n] : SSet.{u}).obj (op (SimplexCategory.mk 0)) :=
      ⟨x, vertex_mem_boundary_of_one_le hn x⟩
    have hmemV : verticalOneSimplex x ∈ (prismSrcInitial n).obj _ :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr (by
        rw [verticalOneSimplex_fst]
        exact sigma_zero_mem_boundary_of_one_le hn x))
    have happ2' : (Subcomplex.unionProd.ι₂ ∂Δ[n] face0).app _
          (verticalOneSimplex xb) = ⟨verticalOneSimplex x, hmemV⟩ := by
      apply Subtype.ext
      change (∂Δ[n].ι ▷ Δ[1]).app _ (verticalOneSimplex xb) =
        verticalOneSimplex x
      rw [whiskerRight_app_verticalOneSimplex]
      rfl
    have hedge : F.app _ (verticalOneSimplex x) = H.app _ (verticalOneSimplex xb) := by
      calc F.app _ (verticalOneSimplex x)
          = φ₀.app _ ⟨verticalOneSimplex x, hmemV⟩ :=
            congr($(hF).app _ ⟨verticalOneSimplex x, hmemV⟩)
        _ = H.app _ (verticalOneSimplex xb) := by
            rw [← happ2']
            exact congr($(hι₂).app _ (verticalOneSimplex xb))
    exact (congrArg (fun e => CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm e)) hedge).to_iff.mpr
      (hHvert xb)

/-- Every original scalar boundary admits full relative source-prism extension with cocartesian verticals
  over the arbitrary original base. -/
theorem relativeCocartesianPrismSrcExtension_boundary
    {X B : SSet.{u}} (p : X ⟶ B) [CocartesianFibration p] (n : ℕ) :
    RelativeCocartesianPrismSrcExtension (boundary.{u} n).ι p := by
  by_cases hn : n = 0
  · subst hn
    exact relativeCocartesianPrismSrcExtension_boundary_zero
  · exact relativeCocartesianPrismSrcExtension_boundary_of_one_le (Nat.one_le_iff_ne_zero.mpr hn)

end SSet
