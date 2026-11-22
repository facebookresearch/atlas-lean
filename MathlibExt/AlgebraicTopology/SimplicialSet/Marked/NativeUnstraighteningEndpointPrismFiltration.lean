/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningRelativeCancellation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningMarkedCriticalCells
import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeCartesianPrismBoundary

/-!
# The original target-prism filtration lifts actual native model maps

The original increasing target-prism filtration, each original simplex,
missing-face index, full horn restriction and base map are retained.
Actual coherent-model fibrations give the original native inner and
marked critical-cell lifts. The critical right edge is the original
marked boundary vertical. The original horn pushout extends each whole
stage and the unchanged top comparison gives the whole original prism.
No intrinsic Cartesian-fibration or native-filler outcome is a premise.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same original right outer horn fills from an actual coherent-model fibration and the original marked
critical edge. -/
theorem nativeUnstraightening_fill_originalRightHorn (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (m : ℕ)
    (t : (horn.{u} (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (b : (Δ[m + 2] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet)
    (hsq : t ≫ ((nativeUnstraightening B).map q).left.hom = (horn.{u} (m + 2) (Fin.last (m + 2))).ι ≫ b)
    (hm : (rightHornEdge t).edge ∈ (nativeUnstraighteningTotal B F).marking) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∃ l : (Δ[m + 2] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
      (horn.{u} (m + 2) (Fin.last (m + 2))).ι ≫ l = t ∧ l ≫ ((nativeUnstraightening B).map q).left.hom = b := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  have ht : t.app (op ⦋1⦌) (rightHornEdgeSimplex.{u} m) ∈ (nativeUnstraighteningTotal B F).marking := by
    rw [← rightHornEdge_edge]
    exact hm
  exact nativeUnstraightening_fill_originalFinalHorn B q hq (by omega) rfl t b hsq
    (rightHornEdgeSimplex.{u} m) rfl ht

/-- The original critical right edge is precisely the original marked last boundary vertical, read through the
unchanged whole stage restriction. -/
theorem nativeUnstraightening_endpointPrism_critical_right_edge (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) (m : ℕ)
    {φ : ((prismTgtFilt (m + 1) (m + 1) : (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      (nativeUnstraighteningTotal B F).toSSet}
    {φ₀ : ((prismTgtInitial (m + 1) : (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      (nativeUnstraighteningTotal B F).toSSet}
    (hrestr : Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt (m + 1)) ≫ φ = φ₀)
    (hVert : φ₀.app (op ⦋1⦌)
      ⟨prismVertLast (m + 1), prismVertLast_mem_prismTgtInitial (by omega)⟩ ∈ (nativeUnstraighteningTotal B
        F).marking) :
    (rightHornEdge
      (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
        (prismTau (m + 1) ⟨m + 1, by omega⟩)
        (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
        (prismTgtFilt_preimage_prismTauMap (⟨m + 1, by omega⟩ : Fin (m + 2))) ≫ φ)).edge ∈
      (nativeUnstraighteningTotal B F).marking := by
  have he : (rightHornEdge
      (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
        (prismTau (m + 1) ⟨m + 1, by omega⟩)
        (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
        (prismTgtFilt_preimage_prismTauMap (⟨m + 1, by omega⟩ : Fin (m + 2))) ≫ φ)).edge =
      φ₀.app (op ⦋1⦌) ⟨prismVertLast (m + 1), prismVertLast_mem_prismTgtInitial (by omega)⟩ := by
    rw [rightHornEdge_hornLift_comp]
    exact congr($(hrestr).app _ ⟨prismVertLast (m + 1), prismVertLast_mem_prismTgtInitial (by omega)⟩)
  exact he.symm ▸ hVert

/-- Every same original target-prism stage retains its whole native extension and original base square under an
actual coherent-model fibration. -/
theorem nativeUnstraightening_endpointPrism_filtration (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) {n : ℕ} (hn : 1 ≤ n)
    (φ₀ : ((prismTgtInitial n : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      (nativeUnstraighteningTotal B F).toSSet)
    (K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet)
    (hbase₀ : φ₀ ≫ ((nativeUnstraightening B).map q).left.hom = (prismTgtInitial n).ι ≫ K)
    (hVert : φ₀.app (op ⦋1⦌) ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩ ∈
      (nativeUnstraighteningTotal B F).marking) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ m : ℕ, m ≤ n + 1 →
      ∃ φm : ((prismTgtFilt n m : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
        (nativeUnstraighteningTotal B F).toSSet,
        Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt m) ≫ φm = φ₀ ∧
          φm ≫ ((nativeUnstraightening B).map q).left.hom = (prismTgtFilt n m).ι ≫ K := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq m
  let p : (nativeUnstraighteningTotal B F).toSSet ⟶ (nativeUnstraighteningTotal B G).toSSet :=
    ((nativeUnstraightening B).map q).left.hom
  let _ : InnerFibration p := nativeUnstraightening_map_innerFibration B q hq
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
    · have he : e.hom ≫ (prismTgtInitial n).ι = (prismTgtFilt n 0).ι := by
        dsimp only [e]
        rw [Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι]
      exact (Category.assoc e.hom φ₀ p).trans
        ((congrArg (fun f => e.hom ≫ f) hbase₀).trans
          ((Category.assoc e.hom (prismTgtInitial n).ι K).symm.trans
            (congrArg (fun f => f ≫ K) he)))
  | succ m ih =>
    intro hm
    obtain ⟨φ₁, hφ₁, hφ₁base⟩ := ih (by omega)
    have hmn : m ≤ n := by omega
    let k : Fin (n + 1) := ⟨m, by omega⟩
    have hpre : (prismTgtFilt n m).preimage (yonedaEquiv.symm (prismTau n k)) = Λ[n + 1, k.succ] :=
      prismTgtFilt_preimage_prismTauMap k
    let σG : (Δ[n + 1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet :=
      yonedaEquiv.symm (K.app _ (prismTau n k))
    have hσG : yonedaEquiv.symm (prismTau n k) ≫ K = σG := by
      dsimp only [σG]
      exact yonedaEquiv_symm_comp _ _
    have hsq : (Subcomplex.hornLift (prismTgtFilt n m) (prismTau n k) k.succ hpre ≫ φ₁) ≫ p =
        Λ[n + 1, k.succ].ι ≫ σG := by
      let j := Subcomplex.hornLift (prismTgtFilt n m) (prismTau n k) k.succ hpre
      have hι : j ≫ (prismTgtFilt n m).ι = Λ[n + 1, k.succ].ι ≫ yonedaEquiv.symm (prismTau n k) := by
        exact Subcomplex.hornLift_ι hpre
      exact (Category.assoc j φ₁ p).trans
        ((congrArg (fun f => j ≫ f) hφ₁base).trans
          ((Category.assoc j (prismTgtFilt n m).ι K).symm.trans
            ((congrArg (fun f => f ≫ K) hι).trans
              ((Category.assoc Λ[n + 1, k.succ].ι (yonedaEquiv.symm (prismTau n k)) K).trans
                (congrArg (fun f => Λ[n + 1, k.succ].ι ≫ f) hσG)))))
    obtain ⟨σF, hσF, hσFbase⟩ : ∃ σF : (Δ[n + 1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
        Subcomplex.hornLift (prismTgtFilt n m) (prismTau n k) k.succ hpre ≫ φ₁ =
          Λ[n + 1, k.succ].ι ≫ σF ∧ σF ≫ p = σG := by
      by_cases hlast : m = n
      · subst m
        obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
        obtain ⟨σF, hσF, hσFbase⟩ := nativeUnstraightening_fill_originalRightHorn B q d _ σG hsq
          (nativeUnstraightening_endpointPrism_critical_right_edge B F d hφ₁ hVert) hq
        exact ⟨σF, hσF.symm, hσFbase⟩
      · have hi : (0 : Fin (n + 2)) < k.succ := by
          rw [Fin.lt_def, Fin.val_succ]
          change 0 < m + 1
          omega
        have hi' : k.succ < Fin.last (n + 1) := by
          rw [Fin.lt_def, Fin.val_succ, Fin.val_last]
          change m + 1 < n + 1
          omega
        let h : HasLiftingProperty Λ[n + 1, k.succ].ι p := InnerFibration.mem _ (horn_ι_mem_innerHornInclusions hi hi')
        obtain ⟨σF, hσF, hσFbase⟩ := h.sq_hasLift (CommSq.mk hsq)
        exact ⟨σF, hσF.symm, hσFbase⟩
    obtain ⟨φ', hφ'1, hφ'2⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
      (fun h => injective_of_mono _ h) φ₁ σF hσF
    have hφ'base : φ' ≫ p = (prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)).ι ≫ K := by
      apply Subcomplex.hom_ext_sup_of_simplex
      · let j := Subcomplex.homOfLE
          (show prismTgtFilt n m ≤ prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k) from le_sup_left)
        have hι : j ≫ (prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)).ι = (prismTgtFilt n m).ι :=
          Subcomplex.homOfLE_ι _
        exact (Category.assoc j φ' p).symm.trans
          ((congrArg (fun f => f ≫ p) hφ'1).trans
            (hφ₁base.trans ((congrArg (fun f => f ≫ K) hι.symm).trans
              (Category.assoc j (prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)).ι K))))
      · let j := Subcomplex.simplexLiftSup (prismTgtFilt n m) (prismTau n k)
        have hι : j ≫ (prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)).ι =
            yonedaEquiv.symm (prismTau n k) := Subcomplex.simplexLiftSup_ι
        exact (Category.assoc j φ' p).symm.trans
          ((congrArg (fun f => f ≫ p) hφ'2).trans
            (hσFbase.trans (hσG.symm.trans
              ((congrArg (fun f => f ≫ K) hι.symm).trans
                (Category.assoc j (prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)).ι K)))))
    let e := Subcomplex.eqToIso (prismTgtFilt_succ_eq_sup.{u} hmn)
    refine ⟨e.hom ≫ φ', ?_, ?_⟩
    · have hcomp : Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt (m + 1)) ≫ e.hom =
        Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt m) ≫
          Subcomplex.homOfLE (show prismTgtFilt n m ≤ prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k) from
            le_sup_left) := by
        dsimp only [e]
        rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
        simp only [Category.assoc, Subcomplex.homOfLE_ι]
        rfl
      rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
      exact hφ₁
    · have he : e.hom ≫ (prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)).ι =
          (prismTgtFilt n (m + 1)).ι := by
        dsimp only [e]
        rw [Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι]
      exact (Category.assoc e.hom φ' p).trans
        ((congrArg (fun f => e.hom ≫ f) hφ'base).trans
          ((Category.assoc e.hom (prismTgtFilt n m ⊔ Subcomplex.ofSimplex (prismTau n k)).ι K).symm.trans
            (congrArg (fun f => f ≫ K) he)))

/-- The unchanged original top-filtration comparison retains the entire original prism and both whole native
equations. -/
theorem nativeUnstraightening_endpointPrism_entire (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) {n : ℕ} (hn : 1 ≤ n)
    (φ₀ : ((prismTgtInitial n : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      (nativeUnstraighteningTotal B F).toSSet)
    (K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet)
    (hbase₀ : φ₀ ≫ ((nativeUnstraightening B).map q).left.hom = (prismTgtInitial n).ι ≫ K)
    (hVert : φ₀.app (op ⦋1⦌) ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩ ∈
      (nativeUnstraighteningTotal B F).marking) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∃ l : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B F).toSSet,
      (prismTgtInitial n).ι ≫ l = φ₀ ∧ l ≫ ((nativeUnstraightening B).map q).left.hom = K := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let p : (nativeUnstraighteningTotal B F).toSSet ⟶ (nativeUnstraighteningTotal B G).toSSet :=
    ((nativeUnstraightening B).map q).left.hom
  obtain ⟨φm, hφm, hφmbase⟩ := nativeUnstraightening_endpointPrism_filtration B q hn φ₀ K hbase₀ hVert hq (n + 1) le_rfl
  let e : ((prismTgtFilt n (n + 1) : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
      (Δ[n] ⊗ Δ[1] : SSet.{u}) := Subcomplex.eqToIso prismTgtFilt_top ≪≫ Subcomplex.topIso _
  have hhom : e.hom = (prismTgtFilt n (n + 1)).ι := by
    dsimp only [e]
    rw [Iso.trans_hom, Subcomplex.eqToIso_hom, Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
  have hι : (prismTgtInitial n).ι = Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt (n + 1)) ≫ e.hom := by
    rw [hhom]
    exact (Subcomplex.homOfLE_ι _).symm
  refine ⟨e.inv ≫ φm, ?_, ?_⟩
  · rw [hι, Category.assoc, ← Category.assoc e.hom e.inv φm, Iso.hom_inv_id, Category.id_comp]
    exact hφm
  · have hmap : φm ≫ p = e.hom ≫ K := hφmbase.trans (congrArg (fun f => f ≫ K) hhom.symm)
    exact (Category.assoc e.inv φm p).trans
      ((congrArg (fun f => e.inv ≫ f) hmap).trans
        ((Category.assoc e.inv e.hom K).symm.trans
          ((congrArg (fun f => f ≫ K) e.inv_hom_id).trans (Category.id_comp K))))

end SSet.Marked
