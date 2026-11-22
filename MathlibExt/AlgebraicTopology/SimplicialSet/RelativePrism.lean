/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PrismVerticals
public import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLifting
public import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeSpecialOuterHorn
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseUnconditional
import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat
import MathlibExt.AlgebraicTopology.SimplicialSet.SSetCoproducts
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# Relative equivalence prism extension

A monomorphism admits extension of an equivalence prism along an inner
fibration with quasicategory target and strict source equivalence lifting.
The extension retains its restriction, source, and the entire prescribed
base prism, and every vertical remains an equivalence.

This is the covering homotopy extension property of Joyal Proposition 5.18
(*The Theory of Quasi-Categories and its Applications*, February 2008,
pp. 287–288). Equivalence verticals express the quasi-invertible homotopies
of that proposition (Corollary 5.12). The proof here uses the boundary-cell
prism filtration directly: strict lifting at newly attached vertices,
relative outer horns in positive dimensions, and the native relative
skeletal tower for a monomorphism. The source is a quasicategory by
innerness and the quasicategory target.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace SSet

private lemma Subcomplex.simplexLiftSup_ι_relativePrism
    {Z : SSet.{u}} {S : Z.Subcomplex} {m : ℕ}
    {z : Z.obj (op (SimplexCategory.mk m))} :
    S.simplexLiftSup z ≫ (S ⊔ Subcomplex.ofSimplex z).ι =
      yonedaEquiv.symm z :=
  rfl

private lemma Subcomplex.hom_ext_sup_of_simplex
    {Z W : SSet.{u}} {S : Z.Subcomplex} {m : ℕ}
    {z : Z.obj (op (SimplexCategory.mk m))}
    {f g : ((S ⊔ Subcomplex.ofSimplex z : Z.Subcomplex) : SSet.{u}) ⟶ W}
    (hS : Subcomplex.homOfLE (show S ≤ S ⊔ Subcomplex.ofSimplex z from
      le_sup_left) ≫ f =
        Subcomplex.homOfLE (show S ≤ S ⊔ Subcomplex.ofSimplex z from
          le_sup_left) ≫ g)
    (hz : S.simplexLiftSup z ≫ f = S.simplexLiftSup z ≫ g) :
    f = g := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  rintro ⟨x, hxSup⟩
  have hx := hxSup
  rw [Subfunctor.max_obj] at hx
  rcases hx with hx | hx
  · let xS : S.obj d := ⟨x, hx⟩
    have hinc : (Subcomplex.homOfLE (show S ≤
          S ⊔ Subcomplex.ofSimplex z from le_sup_left)).app d xS =
        (⟨x, hxSup⟩ : (S ⊔ Subcomplex.ofSimplex z).obj d) := by
      apply Subtype.ext
      rfl
    simpa only [NatTrans.comp_app, types_comp_apply, hinc] using
      congr($(hS).app d xS)
  · have heq : Subcomplex.ofSimplex z =
        Subcomplex.range (yonedaEquiv.symm z) := by
      rw [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
    rw [heq, Subfunctor.range_obj] at hx
    obtain ⟨s, hs⟩ := hx
    have hinc : (S.simplexLiftSup z).app d s =
        (⟨x, hxSup⟩ : (S ⊔ Subcomplex.ofSimplex z).obj d) := by
      apply Subtype.ext
      exact hs
    simpa only [NatTrans.comp_app, types_comp_apply, hinc] using
      congr($(hz).app d s)

private lemma exists_relative_extension_prismSrcFilt_of_one_le
    {X Y : SSet.{u}} {p : X ⟶ Y} [InnerFibration p] [Quasicategory Y]
    {n : ℕ} (hn : 1 ≤ n)
    (φ₀ : ((prismSrcInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X)
    (K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ Y)
    (hbase₀ : φ₀ ≫ p = (prismSrcInitial n).ι ≫ K)
    (hVert : (Edge.mk' (φ₀.app _ ⟨prismVertZero n,
        prismVertZero_mem_prismSrcInitial hn⟩)).IsEquivalence) :
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
          exists_fill_relativeSpecialOuterHorn_of_isEquivalence
            SpecialOuterHornEndpoint.zero _ σY hsq
              (isEquivalence_leftHornEdge_prismSrcStep m' hφ₁ hVert)
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
          Subcomplex.simplexLiftSup_ι_relativePrism]
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
    {X Y : SSet.{u}} {p : X ⟶ Y} [InnerFibration p] [Quasicategory Y]
    {n : ℕ} (hn : 1 ≤ n)
    (φ₀ : ((prismSrcInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X)
    (K : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ Y)
    (hbase₀ : φ₀ ≫ p = (prismSrcInitial n).ι ≫ K)
    (hVert : (Edge.mk' (φ₀.app _ ⟨prismVertZero n,
        prismVertZero_mem_prismSrcInitial hn⟩)).IsEquivalence) :
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

/-- Source-prescribed relative equivalence-prism extension along `i`, with the
entire base prism retained. The base-vertical condition is needed at newly
attached vertices; in positive-dimensional boundary cells every vertex is
already on the boundary. -/
def RelativePrismSrcExtension {A B X Y : SSet.{u}}
    (i : A ⟶ B) (p : X ⟶ Y) : Prop :=
  ∀ (H : A ⊗ Δ[1] ⟶ X) (c : B ⟶ X) (K : B ⊗ Δ[1] ⟶ Y),
    prismSectionAt A 0 ≫ H = i ≫ c →
    prismSectionAt B 0 ≫ K = c ≫ p →
    H ≫ p = (i ▷ Δ[1]) ≫ K →
    PrismOneVerticalsEquivalences H →
    PrismOneVerticalsEquivalences K →
      ∃ F : B ⊗ Δ[1] ⟶ X,
        (i ▷ Δ[1]) ≫ F = H ∧
          prismSectionAt B 0 ≫ F = c ∧
          F ≫ p = K ∧ PrismOneVerticalsEquivalences F

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

/-- The zero-dimensional boundary cell. This is exactly the vertex-adding
case, so it uses strict equivalence-edge lifting rather than a special outer
horn of dimension at least two. -/
private theorem relativePrismSrcExtension_boundary_zero
    {X Y : SSet.{u}} {p : X ⟶ Y} [HasStrictEquivalenceLifting p] :
    RelativePrismSrcExtension ∂Δ[0].ι p := by
  intro H c K _ hKsrc _ _ hKvert
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
  have heK : eK.IsEquivalence := by
    have hval : eK.edge = K.app _
        (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0)) := by
      dsimp only [eK]
      rw [Edge.mk'_edge, yonedaEquiv_comp,
        verticalOneSimplex_deltaZero_eq_yonedaEquiv_leftUnitor_inv]
    exact (hKvert (stdSimplex.obj₀Equiv.symm 0)).of_edge_eq hval.symm
  have hg : g.IsEquivalence := heK.of_edge_eq rfl
  obtain ⟨x₁, hx₁, f, hf, hfmap⟩ :=
    HasStrictEquivalenceLifting.exists_lift g hg
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
    exact hf.of_edge_eq hval.symm

/-- Positive-dimensional boundary-cell case of relative equivalence-prism
extension. This is the outer-horn cell input for the skeletal mono closure. -/
private theorem relativePrismSrcExtension_boundary_of_one_le
    {X Y : SSet.{u}} {p : X ⟶ Y} [InnerFibration p] [Quasicategory Y]
    {n : ℕ} (hn : 1 ≤ n) :
    RelativePrismSrcExtension ∂Δ[n].ι p := by
  intro H c K hHsrc hKsrc hHK hHvert _
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
  have hcritical : (Edge.mk' (φ₀.app _
      ⟨prismVertZero n, prismVertZero_mem_prismSrcInitial hn⟩)).IsEquivalence := by
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (hHvert x0b)
    change φ₀.app _
        ⟨prismVertZero n, prismVertZero_mem_prismSrcInitial hn⟩ =
      H.app _ (verticalOneSimplex x0b)
    rw [← happ2]
    exact congr($(hι₂).app _ (verticalOneSimplex x0b))
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
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (hHvert xb)
    change F.app _ (verticalOneSimplex x) = H.app _ (verticalOneSimplex xb)
    calc F.app _ (verticalOneSimplex x)
        = φ₀.app _ ⟨verticalOneSimplex x, hmemV⟩ :=
          congr($(hF).app _ ⟨verticalOneSimplex x, hmemV⟩)
      _ = H.app _ (verticalOneSimplex xb) := by
          rw [← happ2']
          exact congr($(hι₂).app _ (verticalOneSimplex xb))

/-- Relative equivalence-prism extension for every boundary cell. Dimension
zero is the strict equivalence-lifting case; positive dimensions use the
relative special outer-horn filtration. -/
private theorem relativePrismSrcExtension_boundary
    {X Y : SSet.{u}} {p : X ⟶ Y} [InnerFibration p] [Quasicategory Y]
    [HasStrictEquivalenceLifting p] (n : ℕ) :
    RelativePrismSrcExtension ∂Δ[n].ι p := by
  by_cases hn : n = 0
  · subst hn
    exact relativePrismSrcExtension_boundary_zero
  · exact relativePrismSrcExtension_boundary_of_one_le
      (Nat.one_le_iff_ne_zero.mpr hn)


private lemma relativePrismSrcExtension_of_isPushout
    {A B P Q E S : SSet.{u}}
    {i : A ⟶ B} {f : A ⟶ P} {f' : B ⟶ Q} {j : P ⟶ Q}
    {p : E ⟶ S} (sq : IsPushout i f f' j)
    (h : RelativePrismSrcExtension i p) :
    RelativePrismSrcExtension j p := by
  intro H c K hHsrc hKsrc hHK hHvert hKvert
  have hHsrc₁ : prismSectionAt A 0 ≫ ((f ▷ Δ[1]) ≫ H) =
      i ≫ (f' ≫ c) := by
    calc prismSectionAt A 0 ≫ ((f ▷ Δ[1]) ≫ H)
        = f ≫ (prismSectionAt P 0 ≫ H) := by
          rw [← Category.assoc, prismSectionAt_comp_whiskerRight,
            Category.assoc]
      _ = (f ≫ j) ≫ c := by rw [hHsrc, Category.assoc]
      _ = (i ≫ f') ≫ c := by rw [sq.w]
      _ = i ≫ (f' ≫ c) := Category.assoc _ _ _
  have hKsrc₁ : prismSectionAt B 0 ≫ ((f' ▷ Δ[1]) ≫ K) =
      (f' ≫ c) ≫ p := by
    calc prismSectionAt B 0 ≫ ((f' ▷ Δ[1]) ≫ K)
        = f' ≫ (prismSectionAt Q 0 ≫ K) := by
          rw [← Category.assoc, prismSectionAt_comp_whiskerRight,
            Category.assoc]
      _ = (f' ≫ c) ≫ p := by rw [hKsrc, Category.assoc]
  have hHK₁ : ((f ▷ Δ[1]) ≫ H) ≫ p =
      (i ▷ Δ[1]) ≫ ((f' ▷ Δ[1]) ≫ K) := by
    calc ((f ▷ Δ[1]) ≫ H) ≫ p
        = (f ▷ Δ[1]) ≫ ((j ▷ Δ[1]) ≫ K) := by
          rw [Category.assoc, hHK]
      _ = ((f ≫ j) ▷ Δ[1]) ≫ K := by
          rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
      _ = ((i ≫ f') ▷ Δ[1]) ≫ K := by rw [sq.w]
      _ = (i ▷ Δ[1]) ≫ ((f' ▷ Δ[1]) ≫ K) := by
          rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
  obtain ⟨F₁, hF₁r, hF₁s, hF₁base, hF₁vert⟩ :=
    h ((f ▷ Δ[1]) ≫ H) (f' ≫ c) ((f' ▷ Δ[1]) ≫ K)
      hHsrc₁ hKsrc₁ hHK₁
      (prismOneVerticalsEquivalences_whiskerRight_comp f H hHvert)
      (prismOneVerticalsEquivalences_whiskerRight_comp f' K hKvert)
  let sq₁ := (tensorRight Δ[1]).map_isPushout sq
  let F := sq₁.desc F₁ H hF₁r
  have hFf' : (f' ▷ Δ[1]) ≫ F = F₁ := sq₁.inl_desc F₁ H hF₁r
  have hFj : (j ▷ Δ[1]) ≫ F = H := sq₁.inr_desc F₁ H hF₁r
  have hFbase : F ≫ p = K := by
    apply sq₁.hom_ext
    · calc (f' ▷ Δ[1]) ≫ (F ≫ p)
          = ((f' ▷ Δ[1]) ≫ F) ≫ p := by rw [Category.assoc]
        _ = (f' ▷ Δ[1]) ≫ K := by rw [hFf', hF₁base]
    · calc (j ▷ Δ[1]) ≫ (F ≫ p)
          = ((j ▷ Δ[1]) ≫ F) ≫ p := by rw [Category.assoc]
        _ = (j ▷ Δ[1]) ≫ K := by rw [hFj, hHK]
  refine ⟨F, hFj, ?_, hFbase, ?_⟩
  · apply sq.hom_ext
    · calc f' ≫ (prismSectionAt Q 0 ≫ F)
          = prismSectionAt B 0 ≫ ((f' ▷ Δ[1]) ≫ F) := by
            rw [← Category.assoc,
              ← prismSectionAt_comp_whiskerRight, Category.assoc]
        _ = f' ≫ c := by rw [hFf', hF₁s]
    · calc j ≫ (prismSectionAt Q 0 ≫ F)
          = prismSectionAt P 0 ≫ ((j ▷ Δ[1]) ≫ F) := by
            rw [← Category.assoc,
              ← prismSectionAt_comp_whiskerRight, Category.assoc]
        _ = j ≫ c := by rw [hFj, hHsrc]
  · intro y
    have hy : (∃ b : B _⦋0⦌, f'.app _ b = y) ∨
        (∃ x : P _⦋0⦌, j.app _ x = y) := by
      obtain ⟨k, z, hz⟩ := Types.jointly_surjective_of_isColimit
        ((sq.map ((evaluation SimplexCategoryᵒᵖ (Type u)).obj
          (op ⦋0⦌))).isColimit) y
      cases k with
      | none => exact Or.inl ⟨i.app _ z, hz⟩
      | some k =>
        cases k with
        | left => exact Or.inl ⟨z, hz⟩
        | right => exact Or.inr ⟨z, hz⟩
    rcases hy with ⟨b, hb⟩ | ⟨x, hx⟩
    · refine (Edge.isEquivalence_iff_of_edge_eq (e :=
          Edge.mk' (F.app _ (verticalOneSimplex y))) (e' :=
          Edge.mk' (F₁.app _ (verticalOneSimplex b))) ?_).2 (hF₁vert b)
      change F.app _ (verticalOneSimplex y) =
        F₁.app _ (verticalOneSimplex b)
      calc F.app _ (verticalOneSimplex y)
          = ((f' ▷ Δ[1]) ≫ F).app _ (verticalOneSimplex b) := by
            change F.app _ (verticalOneSimplex y) =
              F.app _ ((f' ▷ Δ[1]).app _ (verticalOneSimplex b))
            rw [whiskerRight_app_verticalOneSimplex, hb]
        _ = F₁.app _ (verticalOneSimplex b) :=
          congr($(hFf').app _ (verticalOneSimplex b))
    · refine (Edge.isEquivalence_iff_of_edge_eq (e :=
          Edge.mk' (F.app _ (verticalOneSimplex y))) (e' :=
          Edge.mk' (H.app _ (verticalOneSimplex x))) ?_).2 (hHvert x)
      change F.app _ (verticalOneSimplex y) = H.app _ (verticalOneSimplex x)
      calc F.app _ (verticalOneSimplex y)
          = ((j ▷ Δ[1]) ≫ F).app _ (verticalOneSimplex x) := by
            change F.app _ (verticalOneSimplex y) =
              F.app _ ((j ▷ Δ[1]).app _ (verticalOneSimplex x))
            rw [whiskerRight_app_verticalOneSimplex, hx]
        _ = H.app _ (verticalOneSimplex x) :=
          congr($(hFj).app _ (verticalOneSimplex x))

private lemma relativePrismSrcExtension_sigmaMap
    {I : Type u} {Aseq Bseq : I → SSet.{u}} {E S : SSet.{u}} {p : E ⟶ S}
    {i : ∀ k, Aseq k ⟶ Bseq k}
    (h : ∀ k, RelativePrismSrcExtension (i k) p) :
    RelativePrismSrcExtension (Limits.Sigma.map i) p := by
  intro H c K hHsrc hKsrc hHK hHvert hKvert
  have hHsrc_k : ∀ k, prismSectionAt (Aseq k) 0 ≫
        ((Sigma.ι Aseq k ▷ Δ[1]) ≫ H) =
      i k ≫ (Sigma.ι Bseq k ≫ c) := by
    intro k
    calc prismSectionAt (Aseq k) 0 ≫
          ((Sigma.ι Aseq k ▷ Δ[1]) ≫ H)
        = Sigma.ι Aseq k ≫ (prismSectionAt (∐ Aseq) 0 ≫ H) := by
          rw [← Category.assoc, prismSectionAt_comp_whiskerRight,
            Category.assoc]
      _ = i k ≫ (Sigma.ι Bseq k ≫ c) := by
          rw [hHsrc, ← Category.assoc, Limits.Sigma.ι_map, Category.assoc]
  have hKsrc_k : ∀ k, prismSectionAt (Bseq k) 0 ≫
        ((Sigma.ι Bseq k ▷ Δ[1]) ≫ K) =
      (Sigma.ι Bseq k ≫ c) ≫ p := by
    intro k
    calc prismSectionAt (Bseq k) 0 ≫
          ((Sigma.ι Bseq k ▷ Δ[1]) ≫ K)
        = Sigma.ι Bseq k ≫ (prismSectionAt (∐ Bseq) 0 ≫ K) := by
          rw [← Category.assoc, prismSectionAt_comp_whiskerRight,
            Category.assoc]
      _ = (Sigma.ι Bseq k ≫ c) ≫ p := by
          rw [hKsrc, Category.assoc]
  have hHK_k : ∀ k, ((Sigma.ι Aseq k ▷ Δ[1]) ≫ H) ≫ p =
      (i k ▷ Δ[1]) ≫ ((Sigma.ι Bseq k ▷ Δ[1]) ≫ K) := by
    intro k
    calc ((Sigma.ι Aseq k ▷ Δ[1]) ≫ H) ≫ p
        = (Sigma.ι Aseq k ▷ Δ[1]) ≫
            (((Limits.Sigma.map i) ▷ Δ[1]) ≫ K) := by
          rw [Category.assoc, hHK]
      _ = ((Sigma.ι Aseq k ≫ Limits.Sigma.map i) ▷ Δ[1]) ≫ K := by
          rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
      _ = ((i k ≫ Sigma.ι Bseq k) ▷ Δ[1]) ≫ K := by
          rw [Limits.Sigma.ι_map]
      _ = (i k ▷ Δ[1]) ≫
            ((Sigma.ι Bseq k ▷ Δ[1]) ≫ K) := by
          rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
  have key : ∀ k, ∃ F : Bseq k ⊗ Δ[1] ⟶ E,
      (i k ▷ Δ[1]) ≫ F = (Sigma.ι Aseq k ▷ Δ[1]) ≫ H ∧
        prismSectionAt (Bseq k) 0 ≫ F = Sigma.ι Bseq k ≫ c ∧
        F ≫ p = (Sigma.ι Bseq k ▷ Δ[1]) ≫ K ∧
          PrismOneVerticalsEquivalences F := fun k ↦
    h k _ _ _ (hHsrc_k k) (hKsrc_k k) (hHK_k k)
      (prismOneVerticalsEquivalences_whiskerRight_comp _ H hHvert)
      (prismOneVerticalsEquivalences_whiskerRight_comp _ K hKvert)
  choose Fseq hF using key
  let hcB := isColimitCofanMkObjOfIsColimit (tensorRight Δ[1])
    Bseq _ (coproductIsCoproduct _)
  let F := hcB.desc (Cofan.mk E Fseq)
  have hFfac : ∀ k, (Sigma.ι Bseq k ▷ Δ[1]) ≫ F = Fseq k :=
    fun k ↦ hcB.fac _ ⟨k⟩
  have hFbase : F ≫ p = K := by
    apply hcB.hom_ext
    rintro ⟨k⟩
    calc (Sigma.ι Bseq k ▷ Δ[1]) ≫ (F ≫ p)
        = ((Sigma.ι Bseq k ▷ Δ[1]) ≫ F) ≫ p := by
          rw [Category.assoc]
      _ = (Sigma.ι Bseq k ▷ Δ[1]) ≫ K := by
          rw [hFfac, (hF k).2.2.1]
  refine ⟨F, ?_, ?_, hFbase, ?_⟩
  · apply (isColimitCofanMkObjOfIsColimit (tensorRight Δ[1])
      Aseq _ (coproductIsCoproduct _)).hom_ext
    rintro ⟨k⟩
    calc (Sigma.ι Aseq k ▷ Δ[1]) ≫
          (((Limits.Sigma.map i) ▷ Δ[1]) ≫ F)
        = (i k ▷ Δ[1]) ≫ ((Sigma.ι Bseq k ▷ Δ[1]) ≫ F) := by
          rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
            Limits.Sigma.ι_map, MonoidalCategory.comp_whiskerRight,
            Category.assoc]
      _ = (Sigma.ι Aseq k ▷ Δ[1]) ≫ H := by
          rw [hFfac, (hF k).1]
  · refine Sigma.hom_ext _ _ (fun k ↦ ?_)
    calc Sigma.ι Bseq k ≫ (prismSectionAt (∐ Bseq) 0 ≫ F)
        = prismSectionAt (Bseq k) 0 ≫
            ((Sigma.ι Bseq k ▷ Δ[1]) ≫ F) := by
          rw [← Category.assoc,
            ← prismSectionAt_comp_whiskerRight, Category.assoc]
      _ = Sigma.ι Bseq k ≫ c := by rw [hFfac, (hF k).2.1]
  · intro y
    obtain ⟨k, x, hx⟩ := exists_sigma_ι_app_eq 0 y
    refine (Edge.isEquivalence_iff_of_edge_eq (e :=
        Edge.mk' (F.app _ (verticalOneSimplex y))) (e' :=
        Edge.mk' ((Fseq k).app _ (verticalOneSimplex x))) ?_).2
      ((hF k).2.2.2 x)
    change F.app _ (verticalOneSimplex y) =
      (Fseq k).app _ (verticalOneSimplex x)
    calc F.app _ (verticalOneSimplex y)
        = ((Sigma.ι Bseq k ▷ Δ[1]) ≫ F).app _
            (verticalOneSimplex x) := by
          change F.app _ (verticalOneSimplex y) =
            F.app _ ((Sigma.ι Bseq k ▷ Δ[1]).app _
              (verticalOneSimplex x))
          rw [whiskerRight_app_verticalOneSimplex, hx]
      _ = (Fseq k).app _ (verticalOneSimplex x) :=
        congr($(hFfac k).app _ (verticalOneSimplex x))

private lemma relativePrismSrcExtension_skeletonStep
    {A B E S : SSet.{u}} (i : A ⟶ B) {p : E ⟶ S}
    [InnerFibration p] [Quasicategory S] [HasStrictEquivalenceLifting p]
    (d : ℕ) :
    RelativePrismSrcExtension (relativeCellComplexOfMono.r i d) p := by
  have hl : RelativePrismSrcExtension
      (relativeCellComplexOfMono.l i d) p :=
    relativePrismSrcExtension_sigmaMap
      (I := relativeCellComplexOfMono.Cell i d)
      (Aseq := fun _ ↦ (∂Δ[d] : SSet.{u}))
      (Bseq := fun _ ↦ Δ[d])
      (i := fun _ ↦ ∂Δ[d].ι)
      (fun _ ↦ relativePrismSrcExtension_boundary d)
  exact relativePrismSrcExtension_of_isPushout
    (relativeCellComplexOfMono.isPushout i d).flip hl

/-- Relative source-prism extension is stable under a sequential colimit:
the base-prism equation is retained at every stage and checked on every leg. -/
private lemma relativePrismSrcExtension_sequential
    {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
    (t : TransfiniteCompositionOfShape ℕ i)
    (hstep : ∀ d, RelativePrismSrcExtension
      (t.F.map (homOfLE (Nat.le_succ d))) p) :
    RelativePrismSrcExtension i p := by
  intro H c K hHsrc hKsrc hHK hHvert hKvert
  have fac0 : t.isoBot.inv ≫
        t.incl.app 0 = i :=
    t.fac
  have hhom0 : t.isoBot.hom ≫ i =
      t.incl.app 0 :=
    by
      calc t.isoBot.hom ≫ i
          = t.isoBot.hom ≫
              (t.isoBot.inv ≫
                t.incl.app 0) := by rw [fac0]
        _ = t.incl.app 0 := by
            rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hstepIncl (d : ℕ) :
      t.F.map (homOfLE (Nat.le_succ d)) ≫
          t.incl.app (d + 1) =
        t.incl.app d := by
    have h : t.F.map (homOfLE (Nat.le_succ d)) ≫
        t.incl.app (d + 1) =
      t.incl.app d ≫ 𝟙 B :=
        t.incl.naturality (homOfLE (Nat.le_succ d))
    exact h.trans (Category.comp_id _)
  let H0 : t.F.obj 0 ⊗ Δ[1] ⟶ X :=
    (t.isoBot.hom ▷ Δ[1]) ≫ H
  have hH0src : prismSectionAt (t.F.obj 0) 0 ≫ H0 =
      t.incl.app 0 ≫ c := by
    calc prismSectionAt (t.F.obj 0) 0 ≫ H0
        = t.isoBot.hom ≫
            (prismSectionAt A 0 ≫ H) := by
          rw [← Category.assoc, prismSectionAt_comp_whiskerRight,
            Category.assoc]
      _ = t.incl.app 0 ≫ c := by
          rw [hHsrc, ← Category.assoc, hhom0]
  have hH0base : H0 ≫ p =
      (t.incl.app 0 ▷ Δ[1]) ≫ K := by
    calc H0 ≫ p
        = (t.isoBot.hom ▷ Δ[1]) ≫
            (((i) ▷ Δ[1]) ≫ K) := by rw [Category.assoc, hHK]
      _ = ((t.isoBot.hom ≫ i) ▷ Δ[1]) ≫
            K := by rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
      _ = (t.incl.app 0 ▷ Δ[1]) ≫ K := by
          rw [hhom0]
  have hH0vert : PrismOneVerticalsEquivalences H0 :=
    prismOneVerticalsEquivalences_whiskerRight_comp _ H hHvert
  have stepEx : ∀ (d : ℕ)
      (Fd : t.F.obj d ⊗ Δ[1] ⟶ X),
      prismSectionAt (t.F.obj d) 0 ≫ Fd =
          t.incl.app d ≫ c →
      Fd ≫ p = (t.incl.app d ▷ Δ[1]) ≫ K →
      PrismOneVerticalsEquivalences Fd →
      ∃ F' : t.F.obj (d + 1) ⊗ Δ[1] ⟶ X,
        ((t.F.map
            (homOfLE (Nat.le_succ d))) ▷ Δ[1]) ≫ F' = Fd ∧
          prismSectionAt (t.F.obj (d + 1)) 0 ≫ F' =
            t.incl.app (d + 1) ≫ c ∧
          F' ≫ p =
            (t.incl.app (d + 1) ▷ Δ[1]) ≫ K ∧
          PrismOneVerticalsEquivalences F' := by
    intro d Fd hsrc hbase hvert
    let step := t.F.map
      (homOfLE (Nat.le_succ d))
    let cnext := t.incl.app (d + 1) ≫ c
    let Knext := (t.incl.app (d + 1) ▷ Δ[1]) ≫ K
    have hsrc' : prismSectionAt (t.F.obj d) 0 ≫ Fd =
        step ≫ cnext := by
      dsimp only [step, cnext]
      rw [hsrc, ← Category.assoc, hstepIncl]
    have hKsrc' : prismSectionAt (t.F.obj (d + 1)) 0 ≫
        Knext = cnext ≫ p := by
      dsimp only [Knext, cnext]
      calc prismSectionAt (t.F.obj (d + 1)) 0 ≫
            ((t.incl.app (d + 1) ▷ Δ[1]) ≫ K)
          = t.incl.app (d + 1) ≫
              (prismSectionAt B 0 ≫ K) := by
            rw [← Category.assoc, prismSectionAt_comp_whiskerRight]
            change t.incl.app (d + 1) ≫
              (prismSectionAt B 0 ≫ K) = _
            rfl
        _ = (t.incl.app (d + 1) ≫ c) ≫ p := by
            rw [hKsrc, Category.assoc]
    have hbase' : Fd ≫ p = (step ▷ Δ[1]) ≫ Knext := by
      dsimp only [step, Knext]
      calc Fd ≫ p
          = (t.incl.app d ▷ Δ[1]) ≫ K := hbase
        _ = ((t.F.map
              (homOfLE (Nat.le_succ d)) ≫
                t.incl.app (d + 1)) ▷ Δ[1]) ≫ K := by
            rw [hstepIncl]
        _ = (t.F.map
              (homOfLE (Nat.le_succ d)) ▷ Δ[1]) ≫
                ((t.incl.app (d + 1) ▷ Δ[1]) ≫ K) := by
            rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    exact hstep d Fd cnext Knext hsrc' hKsrc' hbase' hvert
      (prismOneVerticalsEquivalences_whiskerRight_comp _ K hKvert)
  choose next hnext using stepEx
  let tower : ∀ d, { F : t.F.obj d ⊗ Δ[1] ⟶ X //
      prismSectionAt (t.F.obj d) 0 ≫ F =
          t.incl.app d ≫ c ∧
      F ≫ p = (t.incl.app d ▷ Δ[1]) ≫ K ∧
      PrismOneVerticalsEquivalences F } := fun d ↦
    Nat.rec (motive := fun d ↦
      { F : t.F.obj d ⊗ Δ[1] ⟶ X //
        prismSectionAt (t.F.obj d) 0 ≫ F =
            t.incl.app d ≫ c ∧
        F ≫ p = (t.incl.app d ▷ Δ[1]) ≫ K ∧
        PrismOneVerticalsEquivalences F })
      ⟨H0, hH0src, hH0base, hH0vert⟩
      (fun d ih ↦ ⟨next d ih.1 ih.2.1 ih.2.2.1 ih.2.2.2,
        (hnext d ih.1 ih.2.1 ih.2.2.1 ih.2.2.2).2⟩) d
  have hFsrc : ∀ d, prismSectionAt (t.F.obj d) 0 ≫
        (tower d).1 = t.incl.app d ≫ c :=
    fun d ↦ (tower d).2.1
  have hFbase : ∀ d, (tower d).1 ≫ p =
      (t.incl.app d ▷ Δ[1]) ≫ K :=
    fun d ↦ (tower d).2.2.1
  have hFvert : ∀ d, PrismOneVerticalsEquivalences (tower d).1 :=
    fun d ↦ (tower d).2.2.2
  have hF0 : (tower 0).1 = H0 := rfl
  have hFsucc : ∀ d,
      ((t.F.map (homOfLE (Nat.le_succ d))) ▷ Δ[1]) ≫
          (tower (d + 1)).1 = (tower d).1 :=
    fun d ↦ (hnext d (tower d).1 (hFsrc d) (hFbase d) (hFvert d)).1
  have hcompat : ∀ {d e : ℕ} (h : d ≤ e),
      (t.F.map (homOfLE h) ▷ Δ[1]) ≫
          (tower e).1 = (tower d).1 := by
    intro d e h
    induction h with
    | refl =>
      have e1 : t.F.map
          (homOfLE (Nat.le.refl (n := d))) =
          𝟙 (t.F.obj d) := by
        rw [show homOfLE (Nat.le.refl (n := d)) = 𝟙 d from
          Subsingleton.elim _ _]
        exact CategoryTheory.Functor.map_id _ _
      rw [e1]
      change (tensorRight Δ[1]).map (𝟙 _) ≫ (tower d).1 = (tower d).1
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    | step hde ih =>
      have e2 : t.F.map
          (homOfLE (Nat.le.step hde)) =
          t.F.map (homOfLE hde) ≫
            t.F.map
              (homOfLE (Nat.le_succ _)) := by
        rw [← Functor.map_comp]
        exact congrArg _ (Subsingleton.elim _ _)
      rw [e2, MonoidalCategory.comp_whiskerRight, Category.assoc,
        hFsucc, ih]
  let hc := isColimitOfPreserves (tensorRight Δ[1])
    t.isColimit
  let F : B ⊗ Δ[1] ⟶ X := hc.desc
    { pt := X,
      ι := { app := fun d ↦ (tower d).1,
             naturality := by
               intro d e h
               have hh : h = homOfLE (leOfHom h) := Subsingleton.elim _ _
               rw [hh]
               exact (hcompat (leOfHom h)).trans (Category.comp_id _).symm } }
  have hfac : ∀ d,
      (t.incl.app d ▷ Δ[1]) ≫ F = (tower d).1 :=
    fun d ↦ hc.fac _ d
  have hbaseFinal : F ≫ p = K := by
    apply hc.hom_ext
    intro d
    calc (t.incl.app d ▷ Δ[1]) ≫ (F ≫ p)
        = ((t.incl.app d ▷ Δ[1]) ≫ F) ≫ p := by
          rw [Category.assoc]
      _ = (t.incl.app d ▷ Δ[1]) ≫ K := by
          rw [hfac, hFbase]
  refine ⟨F, ?_, ?_, hbaseFinal, ?_⟩
  · calc (i ▷ Δ[1]) ≫ F
        = (t.isoBot.inv ▷ Δ[1]) ≫ H0 := by
          calc (i ▷ Δ[1]) ≫ F
              = (t.isoBot.inv ▷ Δ[1]) ≫
                  ((t.incl.app 0 ▷ Δ[1]) ≫ F) := by
                rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
                  fac0]
            _ = (t.isoBot.inv ▷ Δ[1]) ≫ H0 := by
                rw [hfac, hF0]
      _ = H := by
          dsimp only [H0]
          rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
            Iso.inv_hom_id]
          change (tensorRight Δ[1]).map (𝟙 _) ≫ H = H
          rw [CategoryTheory.Functor.map_id, Category.id_comp]
  · apply t.isColimit.hom_ext
    intro d
    calc t.incl.app d ≫
          (prismSectionAt B 0 ≫ F)
        = prismSectionAt (t.F.obj d) 0 ≫
            ((t.incl.app d ▷ Δ[1]) ≫ F) := by
          rw [← Category.assoc (prismSectionAt _ 0) _ F,
            ← Category.assoc]
          exact congrArg (fun q ↦ q ≫ F)
            (prismSectionAt_comp_whiskerRight
              (t.incl.app d) (m := 1) 0).symm
      _ = t.incl.app d ≫ c := by
          rw [hfac, hFsrc]
  · intro y
    obtain ⟨d, x, hx⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)) t.isColimit) y
    change (t.incl.app d).app _ x = y at hx
    refine (Edge.isEquivalence_iff_of_edge_eq (e :=
        Edge.mk' (F.app _ (verticalOneSimplex y))) (e' :=
        Edge.mk' ((tower d).1.app _ (verticalOneSimplex x))) ?_).2
      (hFvert d x)
    change F.app _ (verticalOneSimplex y) =
      (tower d).1.app _ (verticalOneSimplex x)
    calc F.app _ (verticalOneSimplex y)
        = ((t.incl.app d ▷ Δ[1]) ≫ F).app _ (verticalOneSimplex x) := by
          change F.app _ (verticalOneSimplex y) =
            F.app _ ((t.incl.app d ▷ Δ[1]).app _ (verticalOneSimplex x))
          rw [whiskerRight_app_verticalOneSimplex, hx]
      _ = (tower d).1.app _ (verticalOneSimplex x) :=
        congr($(hfac d).app _ (verticalOneSimplex x))

/-- Relative covering homotopy extension along every simplicial
monomorphism. The entire prescribed base prism and equivalence verticals are
retained. -/
theorem relativePrismSrcExtension_of_mono
    {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i] (p : X ⟶ Y)
    [InnerFibration p] [Quasicategory Y] [HasStrictEquivalenceLifting p] :
    RelativePrismSrcExtension i p := by
  apply relativePrismSrcExtension_sequential
    (relativeCellComplexOfMono i).toTransfiniteCompositionOfShape
  intro d
  exact relativePrismSrcExtension_skeletonStep i d

end SSet
