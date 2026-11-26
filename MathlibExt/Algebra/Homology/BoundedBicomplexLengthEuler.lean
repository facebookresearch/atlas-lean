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

public import Mathlib.CategoryTheory.Filtration.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Order.WithBotTop
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import MathlibExt.Algebra.Homology.SpectralSequence.LengthEuler
public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence
public import MathlibExt.Algebra.Homology.FirstQuadrantCollapse
public import MathlibExt.Algebra.Homology.FiniteLengthEuler

/-!
# Lengths and Euler characteristics of bounded bicomplex homology

For a first-quadrant bicomplex K of R-modules, total homology in degree j has a finite
horizontal filtration. Its length equals the sum of the lengths on the antidiagonal of page r
whenever r ≥ j+2; the equality is in extended natural numbers. Finite lengths in every second-
page bidegree imply finite total-homology length in each degree.

If K_{p,q} is zero outside 0≤p≤m and 0≤q≤n, and H_p(H^v_qK) has finite length in that
rectangle, total homology has finite length and vanishes in degrees at least m+n+1. Its Euler
characteristic is ∑_{p≤m,q≤n}(−1)^{p+q}ℓ_R(H_p(H^v_qK)). Taking horizontal homology first
gives the corresponding iterated formula through the canonical total-flip isomorphism. The
ring and module carrier universe levels are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R] {H : ModuleCat.{v} R}

/-- The actual canonical map between consecutive integer filtration stages. -/
private def moduleCatFiltrationStep (F : CategoryTheory.Filtration H EInt) (p : ℕ) :
    F.obj (@WithBotTop.coe ℤ ((p : ℤ) - 1)) ⟶ F.obj ((p : ℤ) : EInt) :=
  (F.toMonoOver.map
    (homOfLE (WithBotTop.coe_monotone (show (p : ℤ) - 1 ≤ p by omega)))).hom.left

private theorem moduleCatFiltrationStep_length (F : CategoryTheory.Filtration H EInt)
    (p : ℕ) :
    Module.length R (F.obj ((p : ℤ) : EInt)) =
      Module.length R (F.obj (@WithBotTop.coe ℤ ((p : ℤ) - 1))) +
        Module.length R (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F p)) := by
  have hm : Mono (moduleCatFiltrationStep F p) := by
    apply mono_of_mono_fac
      (MonoOver.w (F.toMonoOver.map
        (homOfLE (WithBotTop.coe_monotone (show (p : ℤ) - 1 ≤ p by omega)))))
  let C : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.cokernelSequence (moduleCatFiltrationStep F p)
  have : Mono C.f := hm
  have hC : C.ShortExact := { exact := ShortComplex.cokernelSequence_exact _ }
  exact Module.length_eq_add_of_exact C.f.hom C.g.hom hC.moduleCat_injective_f
    hC.moduleCat_surjective_g (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact C |>.mp
      hC.exact)

private theorem moduleCatFiltration_length_eq (F : CategoryTheory.Filtration H EInt) (n : ℕ)
    (hzero : IsZero (F.obj ((-1 : ℤ) : EInt)))
    (hexhaustive : IsIso (F.ι.app ((n : ℤ) : EInt))) :
    Module.length R H = ∑ p ∈ Finset.range (n + 1), Module.length R
      (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F p)) := by
  have hStage (p : ℕ) : Module.length R (F.obj ((p : ℤ) : EInt)) =
      ∑ k ∈ Finset.range (p + 1), Module.length R
        (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F k)) := by
    induction p with
    | zero =>
      have hz : Module.length R (F.obj ((-1 : ℤ) : EInt)) = 0 :=
        Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hzero)
      have hz' : Module.length R (F.obj (@WithBotTop.coe ℤ ((0 : ℤ) - 1))) = 0 := hz
      calc
        Module.length R (F.obj ((0 : ℤ) : EInt)) =
            Module.length R (F.obj (@WithBotTop.coe ℤ ((0 : ℤ) - 1))) +
              Module.length R (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F 0)) :=
          moduleCatFiltrationStep_length F 0
        _ = Module.length R
            (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F 0)) := by rw [hz', zero_add]
        _ = ∑ k ∈ Finset.range (0 + 1),
            Module.length R
              (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F k)) := by simp
    | succ p ih =>
      have hp : @WithBotTop.coe ℤ (((p + 1 : ℕ) : ℤ) - 1) = ((p : ℤ) : EInt) := by
        congr 1
        omega
      have hprev := congrArg (fun i : EInt => Module.length R (F.obj i)) hp
      calc
        Module.length R (F.obj (((p + 1 : ℕ) : ℤ) : EInt)) =
            Module.length R (F.obj (@WithBotTop.coe ℤ (((p + 1 : ℕ) : ℤ) - 1))) +
              Module.length R
                (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F (p + 1))) :=
          moduleCatFiltrationStep_length F (p + 1)
        _ = Module.length R (F.obj ((p : ℤ) : EInt)) +
            Module.length R
              (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F (p + 1))) := by rw [hprev]
        _ = (∑ k ∈ Finset.range (p + 1), Module.length R
            (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F k))) +
              Module.length R
                (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F (p + 1))) := by rw [ih]
        _ = ∑ k ∈ Finset.range (p + 1 + 1), Module.length R
            (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F k)) :=
          (Finset.sum_range_succ (fun k => Module.length R
            (cokernel (C := ModuleCat.{v} R) (moduleCatFiltrationStep F k))) (p + 1)).symm
  have : IsIso (F.ι.app ((n : ℤ) : EInt)) := hexhaustive
  have he : Module.length R (F.obj ((n : ℤ) : EInt)) = Module.length R H :=
    (asIso (F.ι.app ((n : ℤ) : EInt))).toLinearEquiv.length_eq
  exact he.symm.trans (hStage n)

private theorem page_length_ne_top_of_secondPage
    (E : CategoryTheory.SpectralSequence (ModuleCat.{v} R)
      (fun r : ℤ => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1)
    (hE₂ : ∀ pq : ℕ × ℕ, Module.length R ((E.page 2 (by omega)).X pq) ≠ ⊤)
    (t : ℕ) (pq : ℕ × ℕ) :
    Module.length R ((E.page ((t : ℤ) + 2) (by omega)).X pq) ≠ ⊤ := by
  induction t with
  | zero => exact hE₂ pq
  | succ t ih =>
    let e : (E.page ((t : ℤ) + 2) (by omega)).homology pq ≅
        (E.page (((t + 1 : ℕ) : ℤ) + 2) (by omega)).X pq :=
      E.iso ((t : ℤ) + 2) (((t : ℤ) + 2) + 1) pq rfl (by omega) ≪≫
        E.pageXIsoOfEq pq (((t : ℤ) + 2) + 1) (((t + 1 : ℕ) : ℤ) + 2)
          (by omega) (by omega)
    rw [← e.toLinearEquiv.length_eq]
    exact ((E.page ((t : ℤ) + 2) (by omega)).sc pq).moduleCat_homology_length_ne_top ih

variable (K : HomologicalComplex₂ (ModuleCat.{v} R)
  (ComplexShape.down ℕ) (ComplexShape.down ℕ))

/-- The canonical cokernel of a filtration step is its actual associated graded object. -/
private def moduleCatFiltrationGradedIso (p q : ℕ) :
    (cokernel (C := ModuleCat.{v} R)
      (moduleCatFiltrationStep (horizontalTotalHomologyFiltration K (p + q)) p)) ≅
      horizontalTotalHomologyGradedPiece K p q :=
  cokernel.mapIso
    (moduleCatFiltrationStep (horizontalTotalHomologyFiltration K (p + q)) p)
    (horizontalTotalHomologyFiltrationStepMap K p q) (Iso.refl _) (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl)

private theorem moduleCatFiltrationGraded_length (n p : ℕ) (hp : p ≤ n) :
    Module.length R (cokernel (C := ModuleCat.{v} R)
      (moduleCatFiltrationStep (horizontalTotalHomologyFiltration K n) p)) =
      Module.length R (((horizontalFirstQuadrantSpectralSequence K).page
        ((n : ℤ) + 2) (by omega)).X (p, n - p)) := by
  have hdegree : p + (n - p) = n := Nat.add_sub_of_le hp
  have hchange := congrArg (fun k : ℕ => Module.length R
    (cokernel (C := ModuleCat.{v} R)
      (moduleCatFiltrationStep (horizontalTotalHomologyFiltration K k) p))) hdegree
  have hgraded := (moduleCatFiltrationGradedIso K p (n - p)).toLinearEquiv.length_eq
  exact hchange.symm.trans (hgraded.trans
    (horizontalStablePageGradedIso K ((n : ℤ) + 2) (by omega)
      p (n - p) (by omega) (by omega)).toLinearEquiv.length_eq.symm)

/-- The total homology length on its stable antidiagonal.

For n ≥ 0, ℓ_R(H_n(Tot K)) equals ∑_{p=0}^n ℓ_R(E_{n+2}^{p,n−p}). This is an extended-natural
length identity and requires no finiteness hypothesis. -/
theorem horizontalTotalHomology_length_eq_stablePage (n : ℕ) :
    Module.length R ((K.total (ComplexShape.down ℕ)).homology n) =
      ∑ p ∈ Finset.range (n + 1), Module.length R
        (((horizontalFirstQuadrantSpectralSequence K).page ((n : ℤ) + 2)).X (p, n - p)) := by
  let F := horizontalTotalHomologyFiltration K n
  have h := moduleCatFiltration_length_eq F n
    (horizontalTotalHomologyFiltration_obj_isZero_of_neg K (-1) (by omega) n)
    (horizontalTotalHomologyFiltration_exhaustive K n)
  exact h.trans (Finset.sum_congr rfl (fun p hp =>
    moduleCatFiltrationGraded_length K n p (Nat.le_of_lt_succ (Finset.mem_range.mp hp))))

/-- Finite second-page lengths imply finite total-homology length.

If every E₂^{p,q} has finite R-length, each H_n(Tot K) has finite length, equals the stable-
antidiagonal length sum, and has the corresponding equality of natural-number lengths. -/
theorem horizontalTotalHomology_length_of_secondPage
    (hE₂ : ∀ p q : ℕ, Module.length R
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q)) ≠ ⊤) (n : ℕ) :
    Module.length R ((K.total (ComplexShape.down ℕ)).homology n) ≠ ⊤ ∧
    Module.length R ((K.total (ComplexShape.down ℕ)).homology n) =
      ∑ p ∈ Finset.range (n + 1), Module.length R
        (((horizontalFirstQuadrantSpectralSequence K).page ((n : ℤ) + 2)).X (p, n - p)) ∧
    (Module.length R ((K.total (ComplexShape.down ℕ)).homology n)).toNat =
      ∑ p ∈ Finset.range (n + 1), (Module.length R
        (((horizontalFirstQuadrantSpectralSequence K).page ((n : ℤ) + 2)).X (p, n - p))).toNat := by
  have hEq := horizontalTotalHomology_length_eq_stablePage K n
  have hfin (p : ℕ) (_ : p ∈ Finset.range (n + 1)) :
      Module.length R
        (((horizontalFirstQuadrantSpectralSequence K).page ((n : ℤ) + 2)).X (p, n - p)) ≠ ⊤ :=
    page_length_ne_top_of_secondPage (horizontalFirstQuadrantSpectralSequence K)
      (fun pq => hE₂ pq.1 pq.2) n (p, n - p)
  refine ⟨?_, hEq, ?_⟩
  · rw [hEq]
    exact ENat.sum_ne_top.mpr hfin
  · rw [hEq, ENat.toNat_sum hfin]

/-- A zero bicomplex term gives a zero second-page component.

If K_{p,q} is zero, the second-page object at (p,q) is zero. -/
theorem horizontalSecondPage_isZero_of_term_isZero (p q : ℕ)
    (h : IsZero ((K.X p).X q)) :
    IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q)) := by
  have hv : IsZero ((K.X p).homology q) :=
    ShortComplex.isZero_homology_of_isZero_X₂ ((K.X p).sc q) h
  have hx : IsZero ((K.verticalHomologyComplex q).X p) := hv
  have hh : IsZero ((K.verticalHomologyComplex q).homology p) :=
    ShortComplex.isZero_homology_of_isZero_X₂ ((K.verticalHomologyComplex q).sc p) hx
  exact hh.of_iso (horizontalSecondPageVerticalHorizontalHomologyIso K p q)

/-- Vanishing above the total degree of a bounded rectangle.

If K_{p,q} is zero whenever p>m or q>n, then H_j(Tot K) is zero for j>m+n. -/
theorem horizontalTotalHomology_isZero_of_bounded (m n : ℕ)
    (hbound : ∀ p q : ℕ, m < p ∨ n < q → IsZero ((K.X p).X q))
    (j : ℕ) (hj : m + n < j) : IsZero ((K.total (ComplexShape.down ℕ)).homology j) := by
  have hlen : Module.length R ((K.total (ComplexShape.down ℕ)).homology j) = 0 := by
    rw [horizontalTotalHomology_length_eq_stablePage K j]
    apply Finset.sum_eq_zero
    intro p hp
    have hpj : p ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
    have hzero := horizontalSecondPage_isZero_of_term_isZero K p (j - p)
      (hbound p (j - p) (by omega))
    have hlate := isZero_horizontalPage_add_two_of_isZero_secondPage K p (j - p) j hzero
    exact Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hlate)
  exact ModuleCat.isZero_iff_subsingleton.mpr (Module.length_eq_zero_iff.mp hlen)

private theorem bounded_secondPage_length_ne_top (m n : ℕ)
    (hbound : ∀ p q : ℕ, m < p ∨ n < q → IsZero ((K.X p).X q))
    (hlen : ∀ p ≤ m, ∀ q ≤ n, Module.length R ((K.verticalHomologyComplex q).homology p) ≠ ⊤)
    (p q : ℕ) :
    Module.length R (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q)) ≠ ⊤ := by
  by_cases hpq : p ≤ m ∧ q ≤ n
  · rw [(horizontalSecondPageVerticalHorizontalHomologyIso K p q).toLinearEquiv.length_eq]
    exact hlen p hpq.1 q hpq.2
  · have hz := horizontalSecondPage_isZero_of_term_isZero K p q
      (hbound p q (by omega))
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)]
    exact ENat.zero_ne_top

/-- Finite-length homology data from bounded iterated homology.

For support in the rectangle p≤m,q≤n and finite lengths of H_p(H^v_qK) there, the total
complex has finite-length homology data with cutoff m+n+1. -/
def boundedBicomplexFiniteLengthHomologyData (m n : ℕ)
    (hbound : ∀ p q : ℕ, m < p ∨ n < q → IsZero ((K.X p).X q))
    (hlen : ∀ p ≤ m, ∀ q ≤ n, Module.length R ((K.verticalHomologyComplex q).homology p) ≠ ⊤) :
    HomologicalComplex.FiniteLengthHomologyData R (K.total (ComplexShape.down ℕ)) where
  cutoff := m + n + 1
  length_ne_top j _ := by
    exact (horizontalTotalHomology_length_of_secondPage K
      (bounded_secondPage_length_ne_top K m n hbound hlen) j).1
  vanishes j hj := horizontalTotalHomology_isZero_of_bounded K m n hbound j (by omega)

/-- The total homology length on any sufficiently late page.

For r ≥ j+2, ℓ_R(H_j(Tot K)) equals ∑_{p=0}^j ℓ_R(E_r^{p,j−p}), without a finiteness
assumption. -/
theorem horizontalTotalHomology_length_eq_latePage (j : ℕ) (r : ℤ)
    (hr : (j : ℤ) + 2 ≤ r) :
    Module.length R ((K.total (ComplexShape.down ℕ)).homology j) =
      ∑ p ∈ Finset.range (j + 1), Module.length R
        (((horizontalFirstQuadrantSpectralSequence K).page r (by omega)).X (p, j - p)) := by
  apply (horizontalTotalHomology_length_eq_stablePage K j).trans
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : p ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  exact (horizontalStablePageGradedIso K ((j : ℤ) + 2) (by omega)
    p (j - p) (by omega) (by omega)).toLinearEquiv.length_eq.trans
      (horizontalStablePageGradedIso K r (by omega)
        p (j - p) (by omega) (by omega)).toLinearEquiv.length_eq.symm

private theorem sum_diagonals_eq_rectangle (m n : ℕ) (f : ℕ × ℕ → ℤ)
    (hzero : ∀ p q, m < p ∨ n < q → f (p, q) = 0) :
    (∑ j ∈ Finset.range (m + n + 1), ∑ p ∈ Finset.range (j + 1), f (p, j - p)) =
      ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1), f (p, q) := by
  let triangle := (Finset.range (m + n + 1)).biUnion Finset.HasAntidiagonal.antidiagonal
  let rectangle := Finset.range (m + 1) ×ˢ Finset.range (n + 1)
  have hdis : Set.PairwiseDisjoint {i : ℕ | i ∈ Finset.range (m + n + 1)}
      (Finset.HasAntidiagonal.antidiagonal : ℕ → Finset (ℕ × ℕ)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro pq hi hj
    exact hij ((Finset.HasAntidiagonal.mem_antidiagonal.mp hi).symm.trans
      (Finset.HasAntidiagonal.mem_antidiagonal.mp hj))
  have hsub : rectangle ⊆ triangle := by
    intro pq hpq
    simp only [rectangle, Finset.mem_product, Finset.mem_range] at hpq
    apply Finset.mem_biUnion.mpr
    exact ⟨pq.1 + pq.2, Finset.mem_range.mpr (by omega),
      Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  have hsmall : (∑ pq ∈ rectangle, f pq) = ∑ pq ∈ triangle, f pq := by
    apply Finset.sum_subset hsub
    intro pq _ hpq
    simp only [rectangle, Finset.mem_product, Finset.mem_range] at hpq
    exact hzero pq.1 pq.2 (by omega)
  calc
    (∑ j ∈ Finset.range (m + n + 1), ∑ p ∈ Finset.range (j + 1), f (p, j - p)) =
        ∑ j ∈ Finset.range (m + n + 1), ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal j, f pq :=
      Finset.sum_congr rfl (fun j _ =>
        (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk f j).symm)
    _ = ∑ pq ∈ triangle, f pq := (Finset.sum_biUnion hdis).symm
    _ = ∑ pq ∈ rectangle, f pq := hsmall.symm
    _ = _ := Finset.sum_product _ _ _

/-- The bounded total Euler characteristic equals the second-page Euler sum.

Under the rectangular support and finite iterated-homology length hypotheses, the finite-
length Euler characteristic of Tot K equals the spectral sequence's page-2 length Euler sum
over the rectangle. -/
theorem boundedBicomplex_euler_eq_secondPage (m n : ℕ)
    (hbound : ∀ p q : ℕ, m < p ∨ n < q → IsZero ((K.X p).X q))
    (hlen : ∀ p ≤ m, ∀ q ≤ n, Module.length R ((K.verticalHomologyComplex q).homology p) ≠ ⊤) :
    HomologicalComplex.finiteLengthEulerCharacteristic R
      (boundedBicomplexFiniteLengthHomologyData K m n hbound hlen) =
      (horizontalFirstQuadrantSpectralSequence K).lengthEuler 2 (by omega) m n := by
  let E := horizontalFirstQuadrantSpectralSequence K
  let T := m + n
  let f (pq : ℕ × ℕ) : ℤ := (-1 : ℤ) ^ (pq.1 + pq.2) *
    (Module.length R ((E.page ((T : ℤ) + 2) (by omega)).X pq)).toNat
  have hE₂ := bounded_secondPage_length_ne_top K m n hbound hlen
  have hz₂ (p q : ℕ) (hpq : m < p ∨ n < q) : IsZero ((E.page 2 (by omega)).X (p, q)) :=
    horizontalSecondPage_isZero_of_term_isZero K p q (hbound p q hpq)
  have hfzero (p q : ℕ) (hpq : m < p ∨ n < q) : f (p, q) = 0 := by
    have hz := isZero_horizontalPage_add_two_of_isZero_secondPage K p q T (hz₂ p q hpq)
    have hzlen : Module.length R ((E.page ((T : ℤ) + 2) (by omega)).X (p, q)) = 0 :=
      Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)
    dsimp only [f]
    rw [hzlen]
    simp
  have hLen (j : ℕ) (hj : j ∈ Finset.range (T + 1)) :
      (Module.length R ((K.total (ComplexShape.down ℕ)).homology j)).toNat =
        ∑ p ∈ Finset.range (j + 1),
          (Module.length R ((E.page ((T : ℤ) + 2) (by omega)).X (p, j - p))).toNat := by
    have he := horizontalTotalHomology_length_eq_latePage K j ((T : ℤ) + 2) (by
      have hjT : j ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      omega)
    have hfin (p : ℕ) (_ : p ∈ Finset.range (j + 1)) :
        Module.length R ((E.page ((T : ℤ) + 2) (by omega)).X (p, j - p)) ≠ ⊤ :=
      page_length_ne_top_of_secondPage E (fun pq => hE₂ pq.1 pq.2) T (p, j - p)
    exact (congrArg ENat.toNat he).trans (ENat.toNat_sum hfin)
  have hStep (j : ℕ) (hj : j ∈ Finset.range (T + 1)) :
      (-1 : ℤ) ^ j * (Module.length R ((K.total (ComplexShape.down ℕ)).homology j)).toNat =
        ∑ p ∈ Finset.range (j + 1), f (p, j - p) := by
    rw [hLen j hj, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [f]
    rw [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hp))]
  have hPages := E.lengthEuler_from_secondPage m n
    (fun p _ q _ => hE₂ p q) hz₂ T
  change (∑ j ∈ Finset.range (T + 1), (-1 : ℤ) ^ j *
    (Module.length R ((K.total (ComplexShape.down ℕ)).homology j)).toNat) =
      E.lengthEuler 2 (by omega) m n
  exact (Finset.sum_congr rfl hStep).trans
    ((sum_diagonals_eq_rectangle m n f hfzero).trans hPages.2.2)

/-- The total Euler characteristic from vertical-then-horizontal homology.

For the stated bounded support and finite lengths, χ_R(Tot K) =
∑_{p≤m,q≤n}(−1)^{p+q}ℓ_R(H_p(H^v_qK)). The finite lengths are read as natural numbers in the
integer sum. -/
theorem boundedBicomplex_euler_eq_iterated (m n : ℕ)
    (hbound : ∀ p q : ℕ, m < p ∨ n < q → IsZero ((K.X p).X q))
    (hlen : ∀ p ≤ m, ∀ q ≤ n, Module.length R ((K.verticalHomologyComplex q).homology p) ≠ ⊤) :
    HomologicalComplex.finiteLengthEulerCharacteristic R
      (boundedBicomplexFiniteLengthHomologyData K m n hbound hlen) =
      ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ (p + q) *
        (Module.length R ((K.verticalHomologyComplex q).homology p)).toNat := by
  apply (boundedBicomplex_euler_eq_secondPage K m n hbound hlen).trans
  unfold CategoryTheory.SpectralSequence.lengthEuler
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [(horizontalSecondPageVerticalHorizontalHomologyIso K p q).toLinearEquiv.length_eq]

/-- Finite-length total homology data with horizontal homology first.

If the horizontal-then-vertical iterated homologies have finite length in the support
rectangle, use the flipped bicomplex and canonical total-flip isomorphism to obtain finite-
length total homology data. -/
def boundedBicomplexFiniteLengthHomologyDataHorizontalFirst (m n : ℕ)
    (hbound : ∀ p q : ℕ, m < p ∨ n < q → IsZero ((K.X p).X q))
    (hlen : ∀ p ≤ m, ∀ q ≤ n,
      Module.length R ((K.flip.verticalHomologyComplex p).homology q) ≠ ⊤) :
    HomologicalComplex.FiniteLengthHomologyData R (K.total (ComplexShape.down ℕ)) :=
  (boundedBicomplexFiniteLengthHomologyData K.flip n m
    (fun q p h => by simpa only [flip_X_X] using hbound p q (Or.comm.mp h))
    (fun q hq p hp => hlen p hp q hq)).mapIso R (K.totalFlipIso (ComplexShape.down ℕ))

/-- The total Euler characteristic from horizontal-then-vertical homology.

For the stated support and finite lengths, χ_R(Tot K) equals the signed rectangle sum of
ℓ_R(H_q(K.flip.verticalHomologyComplex p)), with sign (−1)^{p+q}. -/
theorem boundedBicomplex_euler_eq_horizontalFirst (m n : ℕ)
    (hbound : ∀ p q : ℕ, m < p ∨ n < q → IsZero ((K.X p).X q))
    (hlen : ∀ p ≤ m, ∀ q ≤ n,
      Module.length R ((K.flip.verticalHomologyComplex p).homology q) ≠ ⊤) :
    HomologicalComplex.finiteLengthEulerCharacteristic R
      (boundedBicomplexFiniteLengthHomologyDataHorizontalFirst K m n hbound hlen) =
      ∑ p ∈ Finset.range (m + 1), ∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ (p + q) *
        (Module.length R ((K.flip.verticalHomologyComplex p).homology q)).toNat := by
  let hb : ∀ q p : ℕ, n < q ∨ m < p → IsZero ((K.flip.X q).X p) :=
    fun q p h => by simpa only [flip_X_X] using hbound p q (Or.comm.mp h)
  let hf : ∀ q ≤ n, ∀ p ≤ m,
      Module.length R ((K.flip.verticalHomologyComplex p).homology q) ≠ ⊤ :=
    fun q hq p hp => hlen p hp q hq
  let hflip := boundedBicomplexFiniteLengthHomologyData K.flip n m hb hf
  have ht := HomologicalComplex.finiteLengthEulerCharacteristic_mapIso R hflip
    (K.totalFlipIso (ComplexShape.down ℕ))
  apply ht.symm.trans
  apply (boundedBicomplex_euler_eq_iterated K.flip n m hb hf).trans
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Nat.add_comm]

end HomologicalComplex₂
