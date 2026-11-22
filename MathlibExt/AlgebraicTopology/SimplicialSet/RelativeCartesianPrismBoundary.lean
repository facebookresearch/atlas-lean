/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeCocartesianPrismBoundary
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornLifting

/-!
# Whole relative target prisms controlled by Cartesian edges

The original increasing target-prism ladder has one critical final horn.
Its last vertical is Cartesian and fills that full horn over the given
base simplex. Innerness fills the other steps. Degree zero uses the
actual original target-prescribed Cartesian edge lift. The base remains
arbitrary and all original prism faces are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite
open scoped Simplicial

namespace SSet

/-- Every vertical of the whole original prism is Cartesian for this original base map. -/
def PrismOneVerticalsCartesian {T X B : SSet.{u}} (p : X ⟶ B)
    (F : T ⊗ Δ[1] ⟶ X) : Prop :=
  ∀ x : T _⦋0⦌, CartesianEdge.IsPCartesian p
    (yonedaEquiv.symm (F.app _ (verticalOneSimplex x)))

/-- Full target-prescribed relative prism extension retains the original prism, base and Cartesian verticals. -/
def RelativeCartesianPrismTgtExtension {A D X B : SSet.{u}} (i : A ⟶ D) (p : X ⟶ B) : Prop :=
  ∀ (H : A ⊗ Δ[1] ⟶ X) (c : D ⟶ X) (K : D ⊗ Δ[1] ⟶ B),
    prismSectionAt A 1 ≫ H = i ≫ c →
    prismSectionAt D 1 ≫ K = c ≫ p →
    H ≫ p = (i ▷ Δ[1]) ≫ K →
    PrismOneVerticalsCartesian p H →
      ∃ F : D ⊗ Δ[1] ⟶ X,
        (i ▷ Δ[1]) ≫ F = H ∧ prismSectionAt D 1 ≫ F = c ∧
          F ≫ p = K ∧ PrismOneVerticalsCartesian p F

private theorem critical_right_edge (m : ℕ) {X B : SSet.{u}} (p : X ⟶ B)
    {φ : ((prismTgtFilt (m + 1) (m + 1) : (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X}
    {φ₀ : ((prismTgtInitial (m + 1) : (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X}
    (hrestr : Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt (m + 1)) ≫ φ = φ₀)
    (hVert : CartesianEdge.IsPCartesian p (yonedaEquiv.symm (φ₀.app _
      ⟨prismVertLast (m + 1), prismVertLast_mem_prismTgtInitial (by omega)⟩))) :
    CartesianEdge.IsPCartesian p (yonedaEquiv.symm (rightHornEdge
      (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
        (prismTau (m + 1) ⟨m + 1, by omega⟩)
        (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
        (prismTgtFilt_preimage_prismTauMap (⟨m + 1, by omega⟩ : Fin (m + 2))) ≫ φ)).edge) := by
  have h : (rightHornEdge
      (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
        (prismTau (m + 1) ⟨m + 1, by omega⟩)
        (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
        (prismTgtFilt_preimage_prismTauMap (⟨m + 1, by omega⟩ : Fin (m + 2))) ≫ φ)).edge =
      φ₀.app _ ⟨prismVertLast (m + 1), prismVertLast_mem_prismTgtInitial (by omega)⟩ := by
    rw [rightHornEdge_hornLift_comp]
    exact congr($(hrestr).app _ ⟨prismVertLast (m + 1), prismVertLast_mem_prismTgtInitial (by omega)⟩)
  exact h.symm ▸ hVert

private theorem exists_relative_target_filtration
    {X B : SSet.{u}} {p : X ⟶ B} [InnerFibration p]
    {n : ℕ} (hn : 1 ≤ n)
    (φ₀ : ((prismTgtInitial n : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X)
    (K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ B)
    (hbase₀ : φ₀ ≫ p = (prismTgtInitial n).ι ≫ K)
    (hVert : CartesianEdge.IsPCartesian p (yonedaEquiv.symm (φ₀.app _
      ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩))) :
    ∀ (m : ℕ), m ≤ n + 1 →
      ∃ φm : ((prismTgtFilt n m : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X,
        Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt m) ≫ φm = φ₀ ∧
          φm ≫ p = (prismTgtFilt n m).ι ≫ K := by
  intro m
  induction m with
  | zero =>
    intro _
    let e := Subcomplex.eqToIso (prismTgtFilt_zero.{u} (n := n))
    refine ⟨e.hom ≫ φ₀, ?_, ?_⟩
    · have hid : Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt (n := n) 0) ≫ e.hom = 𝟙 _ := by
        dsimp only [e]
        rw [Subcomplex.eqToIso_hom, ← cancel_mono (prismTgtInitial n).ι]
        simp
      rw [← Category.assoc, hid, Category.id_comp]
    · rw [Category.assoc, hbase₀]
      change (e.hom ≫ (prismTgtInitial n).ι) ≫ K = (prismTgtFilt n 0).ι ≫ K
      congr 1
  | succ m ih =>
    intro hm
    obtain ⟨φ₁, hφ₁, hφ₁base⟩ := ih (by omega)
    have hmn : m ≤ n := by omega
    let k : Fin (n + 1) := ⟨m, by omega⟩
    have hpre : (prismTgtFilt n m).preimage (yonedaEquiv.symm (prismTau n k)) = Λ[n + 1, k.succ] :=
      prismTgtFilt_preimage_prismTauMap k
    let σB : (Δ[n + 1] : SSet.{u}) ⟶ B := yonedaEquiv.symm (K.app _ (prismTau n k))
    have hsq : (Subcomplex.hornLift (prismTgtFilt n m) (prismTau n k) k.succ hpre ≫ φ₁) ≫ p =
        Λ[n + 1, k.succ].ι ≫ σB := by
      rw [Category.assoc, hφ₁base]
      change ((Subcomplex.hornLift (prismTgtFilt n m) (prismTau n k) k.succ hpre ≫
        (prismTgtFilt n m).ι) ≫ K) = _
      rw [Subcomplex.hornLift_ι, Category.assoc, yonedaEquiv_symm_comp]
    obtain ⟨σX, hσX, hσXbase⟩ : ∃ σX : (Δ[n + 1] : SSet.{u}) ⟶ X,
        Subcomplex.hornLift (prismTgtFilt n m) (prismTau n k) k.succ hpre ≫ φ₁ =
          Λ[n + 1, k.succ].ι ≫ σX ∧ σX ≫ p = σB := by
      by_cases hlast : m = n
      · subst m
        obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
        obtain ⟨σX, hσX, hσXbase⟩ := CartesianEdge.exists_fill_rightHorn_of_isPCartesian _ σB hsq
          (critical_right_edge d p hφ₁ hVert)
        exact ⟨σX, hσX.symm, hσXbase⟩
      · have hi : (0 : Fin (n + 2)) < k.succ := by
          rw [Fin.lt_def, Fin.val_succ]
          change 0 < m + 1
          omega
        have hi' : k.succ < Fin.last (n + 1) := by
          rw [Fin.lt_def, Fin.val_succ, Fin.val_last]
          change m + 1 < n + 1
          omega
        let h : HasLiftingProperty Λ[n + 1, k.succ].ι p := InnerFibration.mem _ (horn_ι_mem_innerHornInclusions hi hi')
        obtain ⟨σX, hσX, hσXbase⟩ := h.sq_hasLift (CommSq.mk hsq)
        exact ⟨σX, hσX.symm, hσXbase⟩
    obtain ⟨φ', hφ'1, hφ'2⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
      (fun h => injective_of_mono _ h) φ₁ σX hσX
    have hφ'base : φ' ≫ p = (prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)).ι ≫ K := by
      apply Subcomplex.hom_ext_sup_of_simplex
      · simp only [← Category.assoc, hφ'1, hφ₁base, Subcomplex.homOfLE_ι]
      · simp only [← Category.assoc, hφ'2, hσXbase, Subcomplex.simplexLiftSup_ι]
        dsimp only [σB]
        rw [yonedaEquiv_symm_comp]
    let e := Subcomplex.eqToIso (prismTgtFilt_succ_eq_sup.{u} hmn)
    refine ⟨e.hom ≫ φ', ?_, ?_⟩
    · have hcomp : Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt (m + 1)) ≫ e.hom =
        Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt m) ≫
          Subcomplex.homOfLE (show prismTgtFilt n m ≤ prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)
            from le_sup_left) := by
        dsimp only [e]
        rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
        rfl
      rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
      exact hφ₁
    · rw [Category.assoc, hφ'base]
      change (e.hom ≫ (prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)).ι) ≫ K =
        (prismTgtFilt n (m + 1)).ι ≫ K
      congr 1

private theorem exists_relative_target_boundary
    {X B : SSet.{u}} {p : X ⟶ B} [InnerFibration p] {n : ℕ} (hn : 1 ≤ n)
    (φ₀ : ((prismTgtInitial n : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X)
    (K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ B)
    (hbase₀ : φ₀ ≫ p = (prismTgtInitial n).ι ≫ K)
    (hVert : CartesianEdge.IsPCartesian p (yonedaEquiv.symm (φ₀.app _
      ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩))) :
    ∃ F : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      (prismTgtInitial n).ι ≫ F = φ₀ ∧ F ≫ p = K := by
  obtain ⟨φm, hφm, hφmbase⟩ := exists_relative_target_filtration hn φ₀ K hbase₀ hVert (n + 1) le_rfl
  let e : ((prismTgtFilt n (n + 1) : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
      (Δ[n] ⊗ Δ[1] : SSet.{u}) := Subcomplex.eqToIso prismTgtFilt_top ≪≫ Subcomplex.topIso _
  have hhom : e.hom = (prismTgtFilt n (n + 1)).ι := by
    dsimp only [e]
    rw [Iso.trans_hom, Subcomplex.eqToIso_hom, Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
  have hι : (prismTgtInitial n).ι =
      Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt (n + 1)) ≫ e.hom := by
    rw [hhom]
    exact (Subcomplex.homOfLE_ι _).symm
  refine ⟨e.inv ≫ φm, ?_, ?_⟩
  · rw [hι, Category.assoc, ← Category.assoc e.hom e.inv φm, Iso.hom_inv_id, Category.id_comp]
    exact hφm
  · rw [Category.assoc, hφmbase, ← hhom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private lemma prismSectionAt_deltaZero_one :
    prismSectionAt (Δ[0] : SSet.{u}) (1 : Fin 2) =
      stdSimplex.δ (0 : Fin 2) ≫
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

private theorem relativeCartesianPrismTgtExtension_boundary_zero
    {X Y : SSet.{u}} {p : X ⟶ Y} [CartesianFibration p] :
    RelativeCartesianPrismTgtExtension ∂Δ[0].ι p := by
  intro H c K _ hKtgt _ _
  let x₀ : X.obj (op (SimplexCategory.mk 0)) := yonedaEquiv c
  let eK : Edge
      (Y.δ 1 (yonedaEquiv
        ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K)))
      (Y.δ 0 (yonedaEquiv
        ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K))) :=
    Edge.mk' (yonedaEquiv
      ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K))
  have hsource : p.app _ x₀ =
      Y.δ 0 (yonedaEquiv
        ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K)) := by
    dsimp only [x₀]
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← yonedaEquiv_comp]
    congr 1
    calc c ≫ p
        = prismSectionAt (Δ[0] : SSet.{u}) 1 ≫ K := hKtgt.symm
      _ = (stdSimplex.δ (0 : Fin 2) ≫
            (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv) ≫ K := by
          rw [prismSectionAt_deltaZero_one]
      _ = stdSimplex.δ (0 : Fin 2) ≫
            ((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫ K) := by
          rw [Category.assoc]
  let g := eK.ofEq rfl hsource.symm
  obtain ⟨x₁, hx₁, f, hf, hfmap⟩ := CartesianFibration.lift (p := p) x₀ _ g
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
  · rw [prismSectionAt_deltaZero_one]
    dsimp only [F]
    calc
      ((stdSimplex.δ (0 : Fin 2) ≫
          (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv) ≫
            (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom) ≫
          yonedaEquiv.symm f.edge
          = stdSimplex.δ (0 : Fin 2) ≫
              (((stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫
                (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).hom) ≫
                  yonedaEquiv.symm f.edge) := by simp only [Category.assoc]
      _ = stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm f.edge := by
          rw [Iso.inv_hom_id, Category.id_comp]
      _ = yonedaEquiv.symm (X.δ 0 f.edge) := by
          rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      _ = yonedaEquiv.symm x₀ := by rw [f.tgt_eq]
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

private theorem relativeCartesianPrismTgtExtension_boundary_of_one_le
    {X Y : SSet.{u}} {p : X ⟶ Y} [InnerFibration p]
    {n : ℕ} (hn : 1 ≤ n) :
    RelativeCartesianPrismTgtExtension ∂Δ[n].ι p := by
  intro H c K hHsrc hKsrc hHK hHvert
  let face1 : (Δ[1] : SSet.{u}).Subcomplex :=
    SSet.stdSimplex.face {1}
  set cface : Δ[n] ⊗ (face1 : SSet.{u}) ⟶ X :=
    CartesianMonoidalCategory.fst _ _ ≫ c with hcface
  have hw : (∂Δ[n].ι ▷ (face1 : SSet.{u})) ≫ cface =
      ((∂Δ[n] : SSet.{u}) ◁ face1.ι) ≫ H := by
    calc (∂Δ[n].ι ▷ (face1 : SSet.{u})) ≫ cface
        = (CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            ∂Δ[n].ι) ≫ c := by
          rw [hcface, ← Category.assoc]
          congr 1
      _ = CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            (prismSectionAt (∂Δ[n] : SSet.{u}) 1 ≫ H) := by
          rw [Category.assoc, ← hHsrc]
      _ = ((∂Δ[n] : SSet.{u}) ◁ face1.ι) ≫ H := by
          dsimp only [face1]
          rw [whiskerLeft_faceOne_ι, Category.assoc]
  let sq := Subcomplex.unionProd.isPushout ∂Δ[n] face1
  let φ₀ := sq.desc cface H hw
  have hι₁ : Subcomplex.unionProd.ι₁ ∂Δ[n] face1 ≫ φ₀ = cface :=
    sq.inl_desc cface H hw
  have hι₂ : Subcomplex.unionProd.ι₂ ∂Δ[n] face1 ≫ φ₀ = H :=
    sq.inr_desc cface H hw
  have hcfaceBase : cface ≫ p = (Δ[n] ◁ face1.ι) ≫ K := by
    calc cface ≫ p
        = CartesianMonoidalCategory.fst Δ[n] (face1 : SSet.{u}) ≫
            (c ≫ p) := by rw [hcface, Category.assoc]
      _ = CartesianMonoidalCategory.fst Δ[n] (face1 : SSet.{u}) ≫
            (prismSectionAt Δ[n] 1 ≫ K) := by rw [hKsrc]
      _ = (Δ[n] ◁ face1.ι) ≫ K := by
          dsimp only [face1]
          rw [whiskerLeft_faceOne_ι, Category.assoc]
  have hι₁ι : Subcomplex.unionProd.ι₁ ∂Δ[n] face1 ≫
        (prismTgtInitial n).ι = Δ[n] ◁ face1.ι := by
    dsimp only [face1, prismTgtInitial]
    exact Subcomplex.unionProd.ι₁_ι ∂Δ[n] (stdSimplex.face {1})
  have hι₂ι : Subcomplex.unionProd.ι₂ ∂Δ[n] face1 ≫
        (prismTgtInitial n).ι = ∂Δ[n].ι ▷ Δ[1] := by
    dsimp only [face1, prismTgtInitial]
    exact Subcomplex.unionProd.ι₂_ι ∂Δ[n] (stdSimplex.face {1})
  have hbase₀ : φ₀ ≫ p =
      (prismTgtInitial n).ι ≫ K := by
    apply sq.hom_ext
    · simp only [← Category.assoc, hι₁, hcfaceBase, hι₁ι]
    · simp only [← Category.assoc, hι₂, hHK, hι₂ι]
  let x0b : (∂Δ[n] : SSet.{u}).obj (op (SimplexCategory.mk 0)) :=
    ⟨stdSimplex.obj₀Equiv.symm (Fin.last n),
      vertex_mem_boundary_of_one_le hn _⟩
  have happ2 : (Subcomplex.unionProd.ι₂ ∂Δ[n] face1).app _
        (verticalOneSimplex x0b) =
      ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩ := by
    apply Subtype.ext
    change (∂Δ[n].ι ▷ Δ[1]).app _ (verticalOneSimplex x0b) =
      prismVertLast n
    have happx : ∂Δ[n].ι.app _ x0b = stdSimplex.obj₀Equiv.symm (Fin.last n) := rfl
    rw [whiskerRight_app_verticalOneSimplex, happx]
    apply Prod.ext
    · apply stdSimplex.ext
      intro t
      fin_cases t <;> rfl
    · apply stdSimplex.ext
      intro t
      fin_cases t <;> rfl
  have hcriticalEdge : φ₀.app _ ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩ =
      H.app _ (verticalOneSimplex x0b) := by
    rw [← happ2]
    exact congr($(hι₂).app _ (verticalOneSimplex x0b))
  have hcritical : CartesianEdge.IsPCartesian p
      (yonedaEquiv.symm (φ₀.app _ ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩)) :=
    (congrArg (fun e => CartesianEdge.IsPCartesian p (yonedaEquiv.symm e)) hcriticalEdge).to_iff.mpr
      (hHvert x0b)
  obtain ⟨F, hF, hFbase⟩ :=
    exists_relative_target_boundary hn φ₀ K hbase₀ hcritical
  refine ⟨F, ?_, ?_, hFbase, ?_⟩
  · have e₂ : (∂Δ[n].ι ▷ Δ[1]) =
        Subcomplex.unionProd.ι₂ ∂Δ[n] face1 ≫
          (prismTgtInitial n).ι :=
      (Subcomplex.unionProd.ι₂_ι ∂Δ[n] face1).symm
    rw [e₂, Category.assoc, hF, hι₂]
  · apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    have hmemFace : ((prismSectionAt Δ[n] (1 : Fin 2)).app U s).2 ∈
        face1.obj U := by
      subst face1
      change Finset.image
          (stdSimplex.objEquiv
            (((prismSectionAt Δ[n] (1 : Fin 2)).app U s).2)).toOrderHom
            ⊤ ≤ ({1} : Finset (Fin 2))
      rw [Finset.image_subset_iff]
      intro j _
      exact Finset.mem_singleton.2
        (asOrderHom_prismSectionAt_app_snd Δ[n] (1 : Fin 2) s j)
    have hmem : (prismSectionAt Δ[n] 1).app U s ∈
        (prismTgtInitial n).obj U :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl hmemFace)
    let sface : (Δ[n] ⊗ (face1 : SSet.{u})).obj U :=
      (s, ⟨((prismSectionAt Δ[n] 1).app U s).2, hmemFace⟩)
    have happ1 : (Subcomplex.unionProd.ι₁ ∂Δ[n] face1).app U sface =
        ⟨(prismSectionAt Δ[n] 1).app U s, hmem⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact (prismSectionAt_app_fst _ _ s).symm
      · rfl
    change F.app U ((prismSectionAt Δ[n] 1).app U s) = c.app U s
    calc F.app U ((prismSectionAt Δ[n] 1).app U s)
        = φ₀.app U ⟨(prismSectionAt Δ[n] 1).app U s, hmem⟩ :=
          congr($(hF).app U ⟨(prismSectionAt Δ[n] 1).app U s, hmem⟩)
      _ = cface.app U sface := by
          rw [← happ1]
          exact congr($(hι₁).app U sface)
      _ = c.app U s := rfl
  · intro x
    let xb : (∂Δ[n] : SSet.{u}).obj (op (SimplexCategory.mk 0)) :=
      ⟨x, vertex_mem_boundary_of_one_le hn x⟩
    have hmemV : verticalOneSimplex x ∈ (prismTgtInitial n).obj _ :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr (by
        rw [verticalOneSimplex_fst]
        exact sigma_zero_mem_boundary_of_one_le hn x))
    have happ2' : (Subcomplex.unionProd.ι₂ ∂Δ[n] face1).app _
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
    exact (congrArg (fun e => CartesianEdge.IsPCartesian p (yonedaEquiv.symm e)) hedge).to_iff.mpr
      (hHvert xb)


/-- Every original scalar boundary has whole target-prescribed Cartesian prism extension over the arbitrary
  original base. -/
theorem relativeCartesianPrismTgtExtension_boundary
    {X B : SSet.{u}} (p : X ⟶ B) [CartesianFibration p] (n : ℕ) :
    RelativeCartesianPrismTgtExtension (boundary.{u} n).ι p := by
  by_cases hn : n = 0
  · subst hn
    exact relativeCartesianPrismTgtExtension_boundary_zero
  · exact relativeCartesianPrismTgtExtension_boundary_of_one_le (Nat.one_le_iff_ne_zero.mpr hn)

end SSet
