/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

@[expose] public section

section
open scoped CStarAlgebra InnerProduct
open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

-- N1
private theorem cstarMatrix_gram_nonneg
    {n : Type*} [Fintype n]
    {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (v : n → B) :
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => star (v i) * v j) := by
  classical
  rcases isEmpty_or_nonempty n with h | h
  · apply le_of_eq
    apply CStarMatrix.ext
    intro i j
    simp only [CStarMatrix.zero_apply, CStarMatrix.ofMatrix_apply, Matrix.of_apply]
    exact (IsEmpty.false i).elim
  · obtain ⟨i₀⟩ := h
    let R : CStarMatrix n n B :=
      CStarMatrix.ofMatrix (Matrix.of fun k j => if k = i₀ then v j else 0)
    have hRR : star R * R = CStarMatrix.ofMatrix (Matrix.of fun i j => star (v i) * v j) := by
      apply CStarMatrix.ext
      intro i j
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, R,
        CStarMatrix.ofMatrix_apply, Matrix.of_apply]
      have hterm : ∀ k : n, star (if k = i₀ then v i else 0) * (if k = i₀ then v j else 0)
          = if k = i₀ then star (v i) * v j else 0 := by
        intro k
        by_cases hk : k = i₀ <;> simp [hk]
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      rw [Finset.sum_ite_eq' _ i₀ (fun _ => star (v i) * v j)]
      simp
    rw [← hRR]
    exact star_mul_self_nonneg _

-- N2
private theorem cstarMatrix_inner_sum_nonneg
    {n : Type*} [Fintype n]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : CStarMatrix n n (H →L[ℂ] H)) (hP : 0 ≤ P) (w : n → H) :
    0 ≤ ∑ i, ∑ j, ⟪w i, P i j (w j)⟫_ℂ := by
  classical
  rw [StarOrderedRing.nonneg_iff] at hP
  refine AddSubmonoid.closure_induction (fun Q hQ => ?_) ?_ (fun P Q _ _ ihP ihQ => ?_) hP
  · obtain ⟨R, rfl⟩ := hQ
    have entry : ∀ i j : n, ⟪w i, (star R * R) i j (w j)⟫_ℂ
        = ∑ k, ⟪R k i (w i), R k j (w j)⟫_ℂ := by
      intro i j
      rw [CStarMatrix.mul_apply]
      simp only [CStarMatrix.star_apply]
      rw [sum_apply Finset.univ (fun k => star (R k i) * R k j) (w j)]
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    have inner_eq : ∀ k : n, (∑ i, ∑ j, ⟪R k i (w i), R k j (w j)⟫_ℂ)
        = ⟪∑ j, R k j (w j), ∑ j, R k j (w j)⟫_ℂ := by
      intro k
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_sum]
    have step1 : (∑ i, ∑ j, ⟪w i, (star R * R) i j (w j)⟫_ℂ)
        = ∑ i, ∑ j, ∑ k, ⟪R k i (w i), R k j (w j)⟫_ℂ :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => entry i j
    have step2 : (∑ i, ∑ j, ∑ k, ⟪R k i (w i), R k j (w j)⟫_ℂ)
        = ∑ k, ∑ i, ∑ j, ⟪R k i (w i), R k j (w j)⟫_ℂ := by
      calc _ = ∑ i, ∑ k, ∑ j, ⟪R k i (w i), R k j (w j)⟫_ℂ :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    calc (∑ i, ∑ j, ⟪w i, (star R * R) i j (w j)⟫_ℂ)
        = ∑ k, ⟪∑ j, R k j (w j), ∑ j, R k j (w j)⟫_ℂ := by
          rw [step1, step2]
          exact Finset.sum_congr rfl fun k _ => inner_eq k
      _ ≥ 0 := by
          apply Finset.sum_nonneg
          intro k _
          rw [RCLike.nonneg_iff]
          exact ⟨inner_self_nonneg, inner_self_im _⟩
  · simp only [CStarMatrix.zero_apply, zero_apply, inner_zero_right,
      Finset.sum_const_zero, le_refl]
  · have hsum : (∑ i, ∑ j, ⟪w i, (P + Q) i j (w j)⟫_ℂ)
        = (∑ i, ∑ j, ⟪w i, P i j (w j)⟫_ℂ) + (∑ i, ∑ j, ⟪w i, Q i j (w j)⟫_ℂ) := by
      calc (∑ i, ∑ j, ⟪w i, (P + Q) i j (w j)⟫_ℂ)
          = ∑ i, ∑ j, (⟪w i, P i j (w j)⟫_ℂ + ⟪w i, Q i j (w j)⟫_ℂ) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [CStarMatrix.add_apply, add_apply, inner_add_right]
        _ = ∑ i, ((∑ j, ⟪w i, P i j (w j)⟫_ℂ) + (∑ j, ⟪w i, Q i j (w j)⟫_ℂ)) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
        _ = _ := Finset.sum_add_distrib
    rw [hsum]
    exact add_nonneg ihP ihQ

-- N8
private theorem completion_coe_eq_of_inner_eq
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u v : E} (h : ∀ w : E, ⟪w, u⟫_ℂ = ⟪w, v⟫_ℂ) :
    (u : UniformSpace.Completion E) = v := by
  have h0' : ⟪u - v, u - v⟫_ℂ = 0 := by
    rw [inner_sub_right, h (u - v), sub_self]
  have hnorm : ‖u - v‖ = 0 := by
    have hsq : ‖u - v‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ) (u - v), h0', map_zero]
    exact sq_eq_zero_iff.mp hsq
  have hco_norm : ‖(u : UniformSpace.Completion E) - v‖ = 0 := by
    rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe, hnorm]
  exact sub_eq_zero.mp (norm_eq_zero.mp hco_norm)

-- N3
private theorem cp_gram_sum_nonneg
    {A H : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (s : Finset A) (x : A → H) :
    0 ≤ ∑ a ∈ s, ∑ b ∈ s, ⟪x a, φ (star a * b) (x b)⟫_ℂ := by
  classical
  let M : CStarMatrix ↥s ↥s A :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => star (i : A) * (j : A))
  have hM : 0 ≤ M := cstarMatrix_gram_nonneg (n := ↥s) (B := A) (fun i => (i : A))
  have hP : 0 ≤ M.map φ :=
    CompletelyPositiveMap.map_cstarMatrix_nonneg φ M hM
  have hN := cstarMatrix_inner_sum_nonneg (M.map φ) hP (fun i => x (i : A))
  simp only [CStarMatrix.map_apply, M, CStarMatrix.ofMatrix_apply,
    Matrix.of_apply] at hN
  have hgoal : (∑ a ∈ s, ∑ b ∈ s, ⟪x a, φ (star a * b) (x b)⟫_ℂ)
      = ∑ i : ↥s, ∑ j : ↥s, ⟪x ↑i, φ (star ↑i * ↑j) (x ↑j)⟫_ℂ := by
    rw [← Finset.sum_coe_sort s]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_coe_sort s]
  rw [hgoal]
  exact hN

-- N4 definition
private noncomputable def stinespringForm {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f g : A →₀ H) : ℂ :=
  f.sum (fun a x => g.sum (fun b y => ⟪x, φ (star a * b) y⟫_ℂ))

-- N4 (i)
private theorem stinespringForm_add_left {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f f' g : A →₀ H) :
    stinespringForm φ (f + f') g = stinespringForm φ f g + stinespringForm φ f' g := by
  simp only [stinespringForm]
  rw [Finsupp.sum_add_index']
  · intro a
    simp
  · intro a x₁ x₂
    simp only [inner_add_left, Finsupp.sum_add]

-- N4 (ii)
private theorem stinespringForm_smul_left {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (r : ℂ) (f g : A →₀ H) :
    stinespringForm φ (r • f) g = (starRingEnd ℂ) r * stinespringForm φ f g := by
  simp only [stinespringForm]
  rw [Finsupp.sum_smul_index']
  · simp only [inner_smul_left, Finsupp.mul_sum]
  · intro a
    simp

-- N4 (iii)
private theorem stinespringForm_conj_symm {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f g : A →₀ H) :
    (starRingEnd ℂ) (stinespringForm φ g f) = stinespringForm φ f g := by
  have hop : ∀ a b : A, φ (star a * b)
      = ContinuousLinearMap.adjoint (φ (star b * a)) := by
    intro a b
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star φ, star_mul, star_star]
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      (starRingEnd ℂ) ⟪x, φ (star a * b) y⟫_ℂ = ⟪y, φ (star b * a) x⟫_ℂ := by
    intro a x b y
    rw [inner_conj_symm, hop a b, ContinuousLinearMap.adjoint_inner_left]
  simp only [stinespringForm, map_finsuppSum, term]
  exact (Finsupp.sum_comm f g _).symm

-- N4 (iv)
private theorem stinespringForm_single {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a b : A) (x y : H) :
    stinespringForm φ (Finsupp.single a x) (Finsupp.single b y)
      = ⟪x, φ (star a * b) y⟫_ℂ := by
  simp only [stinespringForm]
  rw [Finsupp.sum_single_index (by simp)]
  rw [Finsupp.sum_single_index (by simp [map_zero])]

-- N4 (v)
private theorem stinespringForm_self {A H : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : A →₀ H) :
    stinespringForm φ f f
      = ∑ a ∈ f.support, ∑ b ∈ f.support, ⟪f a, φ (star a * b) (f b)⟫_ℂ := rfl

-- N5 pre-space synonym
@[nolint unusedArguments]
private def StinespringPre (A H : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (_φ : A →CP (H →L[ℂ] H)) := A →₀ H

private noncomputable instance StinespringPre_addCommGroup (A H : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (φ : A →CP (H →L[ℂ] H)) : AddCommGroup (StinespringPre A H φ) :=
  inferInstanceAs (AddCommGroup (A →₀ H))

private noncomputable instance StinespringPre_module (A H : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (φ : A →CP (H →L[ℂ] H)) : Module ℂ (StinespringPre A H φ) :=
  inferInstanceAs (Module ℂ (A →₀ H))

private noncomputable def StinespringPre.toPre (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : (A →₀ H) ≃ₗ[ℂ] StinespringPre A H φ :=
  LinearEquiv.refl ℂ _

private noncomputable def StinespringPre.ofPre (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : StinespringPre A H φ ≃ₗ[ℂ] (A →₀ H) :=
  (StinespringPre.toPre A H φ).symm

private noncomputable abbrev stinespringCore (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : PreInnerProductSpace.Core ℂ (StinespringPre A H φ) where
  inner f g := stinespringForm φ (StinespringPre.ofPre A H φ f) (StinespringPre.ofPre A H φ g)
  conj_inner_symm f g := stinespringForm_conj_symm φ _ _
  re_inner_nonneg f := by
    show 0 ≤ RCLike.re (stinespringForm φ (StinespringPre.ofPre A H φ f)
      (StinespringPre.ofPre A H φ f))
    rw [stinespringForm_self]
    exact RCLike.nonneg_iff.mp
      (cp_gram_sum_nonneg φ (StinespringPre.ofPre A H φ f).support
        ⇑(StinespringPre.ofPre A H φ f)) |>.1
  add_left f g h := by
    change stinespringForm φ (StinespringPre.ofPre A H φ (f + g)) _ = _ + _
    rw [map_add]
    exact stinespringForm_add_left φ _ _ _
  smul_left f g r := by
    change stinespringForm φ (StinespringPre.ofPre A H φ (r • f)) _ = _ * _
    rw [map_smul]
    exact stinespringForm_smul_left φ _ _ _

private noncomputable instance StinespringPre_seminormed (A H : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (φ : A →CP (H →L[ℂ] H)) :
    SeminormedAddCommGroup (StinespringPre A H φ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := stinespringCore A H φ)

private noncomputable instance StinespringPre_inner (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : InnerProductSpace ℂ (StinespringPre A H φ) :=
  InnerProductSpace.ofCore (stinespringCore A H φ)

private theorem stinespring_pre_inner_def (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f g : StinespringPre A H φ) :
    ⟪f, g⟫_ℂ = stinespringForm φ (StinespringPre.ofPre A H φ f)
      (StinespringPre.ofPre A H φ g) := rfl

private theorem stinespring_pre_inner_single (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a b : A) (x y : H) :
    ⟪StinespringPre.toPre A H φ (Finsupp.single a x),
      StinespringPre.toPre A H φ (Finsupp.single b y)⟫_ℂ
      = ⟪x, φ (star a * b) y⟫_ℂ := by
  rw [stinespring_pre_inner_def]
  exact stinespringForm_single φ a b x y

-- N6 auxiliary simp lemmas
@[simp] private theorem StinespringPre.toPre_ofPre (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a : StinespringPre A H φ) :
    StinespringPre.toPre A H φ (StinespringPre.ofPre A H φ a) = a := rfl

@[simp] private theorem StinespringPre.ofPre_toPre (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a : A →₀ H) :
    StinespringPre.ofPre A H φ (StinespringPre.toPre A H φ a) = a := rfl

-- N6 definition
private noncomputable def stinespringLeftMul0 (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) : StinespringPre A H φ →ₗ[ℂ] StinespringPre A H φ :=
  (StinespringPre.toPre A H φ).toLinearMap ∘ₗ
    Finsupp.lmapDomain H ℂ (fun a => c * a) ∘ₗ
      (StinespringPre.ofPre A H φ).toLinearMap

-- N6 Phi definition (right side of inner formula)
private noncomputable def stinespringPhi (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (c : A)
    (g : StinespringPre A H φ) : ℂ :=
  (StinespringPre.ofPre A H φ f).sum (fun a x =>
    (StinespringPre.ofPre A H φ g).sum (fun b y => ⟪x, φ (star a * (c * b)) y⟫_ℂ))

-- N6 (i) mul
private theorem stinespringLeftMul0_mul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c d : A) :
    stinespringLeftMul0 A H φ (c * d)
      = stinespringLeftMul0 A H φ c ∘ₗ stinespringLeftMul0 A H φ d := by
  apply LinearMap.ext
  intro f
  simp only [stinespringLeftMul0, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply, LinearEquiv.coe_coe, StinespringPre.ofPre_toPre]
  rw [← Finsupp.mapDomain_comp]
  have hfun : (fun a : A => (c * d) * a) = ((fun a => c * a) ∘ fun a => d * a) := by
    funext a
    simp only [Function.comp_apply]
    exact mul_assoc c d a
  rw [hfun]

-- N6 (i) one
private theorem stinespringLeftMul0_one (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) :
    stinespringLeftMul0 A H φ 1 = LinearMap.id := by
  apply LinearMap.ext
  intro f
  simp only [stinespringLeftMul0, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
  rw [show (fun a : A => (1 : A) * a) = id from funext fun a => one_mul a]
  rw [Finsupp.mapDomain_id]
  exact StinespringPre.toPre_ofPre A H φ f

-- N6 (ii) inner formula
private theorem stinespringLeftMul0_inner (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f g : StinespringPre A H φ) (c : A) :
    ⟪f, stinespringLeftMul0 A H φ c g⟫_ℂ = stinespringPhi A H φ f c g := by
  have hmid : ∀ (a : A) (x : H),
      ((Finsupp.mapDomain (fun b => c * b) (StinespringPre.ofPre A H φ g)).sum
        (fun b y => ⟪x, φ (star a * b) y⟫_ℂ))
      = ((StinespringPre.ofPre A H φ g).sum
        (fun b y => ⟪x, φ (star a * (c * b)) y⟫_ℂ)) := by
    intro a x
    apply Finsupp.sum_mapDomain_index
    · intro b
      simp [map_zero]
    · intro b y₁ y₂
      show ⟪x, φ (star a * b) (y₁ + y₂)⟫_ℂ = _
      rw [map_add, inner_add_right]
  rw [stinespring_pre_inner_def]
  change stinespringForm φ _ _ = _
  simp only [stinespringForm, stinespringLeftMul0, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply, LinearEquiv.coe_coe, StinespringPre.ofPre_toPre,
    stinespringPhi]
  exact Finsupp.sum_congr (fun a _ => hmid a _)

-- N6 (iii) Phi add
private theorem stinespringPhi_add (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (c d : A)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (c + d) g
      = stinespringPhi A H φ f c g + stinespringPhi A H φ f d g := by
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      ⟪x, φ (star a * ((c + d) * b)) y⟫_ℂ
        = ⟪x, φ (star a * (c * b)) y⟫_ℂ + ⟪x, φ (star a * (d * b)) y⟫_ℂ := by
    intro a x b y
    have harg : star a * ((c + d) * b) = star a * (c * b) + star a * (d * b) := by
      rw [add_mul, mul_add]
    rw [harg, map_add _ _ _, add_apply, inner_add_right]
  simp only [stinespringPhi]
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr (fun a _ => ?_)
  rw [← Finsupp.sum_add]
  exact Finsupp.sum_congr (fun b _ => term a _ b _)

-- N6 (iii) Phi smul
private theorem stinespringPhi_smul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (r : ℂ) (c : A)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (r • c) g = r * stinespringPhi A H φ f c g := by
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      ⟪x, φ (star a * ((r • c) * b)) y⟫_ℂ = r * ⟪x, φ (star a * (c * b)) y⟫_ℂ := by
    intro a x b y
    have harg : star a * ((r • c) * b) = r • (star a * (c * b)) := by
      rw [smul_mul_assoc, mul_smul_comm]
    rw [harg, map_smul, smul_apply, inner_smul_right]
  simp only [stinespringPhi]
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun a _ => ?_)
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr (fun b _ => term a _ b _)

-- N6 (iii) Phi one
private theorem stinespringPhi_one (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f g : StinespringPre A H φ) :
    stinespringPhi A H φ f 1 g = ⟪f, g⟫_ℂ := by
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      ⟪x, φ (star a * (1 * b)) y⟫_ℂ = ⟪x, φ (star a * b) y⟫_ℂ := by
    intro a x b y
    rw [one_mul]
  rw [stinespring_pre_inner_def]
  change stinespringPhi A H φ f 1 g = stinespringForm φ _ _
  simp only [stinespringPhi, stinespringForm]
  exact Finsupp.sum_congr (fun a _ => Finsupp.sum_congr (fun b _ => term a _ b _))

-- N6 (iv) adjoint
private theorem stinespringLeftMul0_adj (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) (f g : StinespringPre A H φ) :
    ⟪stinespringLeftMul0 A H φ c f, g⟫_ℂ
      = ⟪f, stinespringLeftMul0 A H φ (star c) g⟫_ℂ := by
  have hop : ∀ a b : A, φ (star a * (c * b))
      = ContinuousLinearMap.adjoint (φ (star b * ((star c) * a))) := by
    intro a b
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star φ, star_mul, star_star, star_mul,
      star_star, mul_assoc]
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      (starRingEnd ℂ) ⟪x, φ (star a * (c * b)) y⟫_ℂ
        = ⟪y, φ (star b * ((star c) * a)) x⟫_ℂ := by
    intro a x b y
    rw [inner_conj_symm, hop a b, ContinuousLinearMap.adjoint_inner_left]
  have hswap : (starRingEnd ℂ) (stinespringPhi A H φ g c f)
      = stinespringPhi A H φ f (star c) g := by
    simp only [stinespringPhi, map_finsuppSum, term]
    exact (Finsupp.sum_comm _ _ _).symm
  rw [← inner_conj_symm, stinespringLeftMul0_inner, hswap,
    ← stinespringLeftMul0_inner]

-- N7 Phi neg / sub helpers
private theorem stinespringPhi_neg (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (c : A)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (-c) g = -stinespringPhi A H φ f c g := by
  have hneg : (-1 : ℂ) • c = -c := by rw [neg_smul, one_smul]
  rw [← hneg, stinespringPhi_smul, neg_one_mul]

private theorem stinespringPhi_sub (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (c d : A)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (c - d) g
      = stinespringPhi A H φ f c g - stinespringPhi A H φ f d g := by
  rw [sub_eq_add_neg, stinespringPhi_add, stinespringPhi_neg, sub_eq_add_neg]

private theorem stinespringPhi_algebraMap (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (t : ℝ)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (algebraMap ℝ A t) g = (t : ℂ) * ⟪f, g⟫_ℂ := by
  rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, stinespringPhi_smul,
    stinespringPhi_one]

-- N7 norm bound
private theorem stinespringLeftMul0_bound (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) (f : StinespringPre A H φ) :
    ‖stinespringLeftMul0 A H φ c f‖ ≤ ‖c‖ * ‖f‖ := by
  have hpos : ∀ d : A, 0 ≤ d →
      0 ≤ RCLike.re (stinespringPhi A H φ f d f) := by
    intro d hd
    obtain ⟨s, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hd
    rw [← stinespringLeftMul0_inner, stinespringLeftMul0_mul]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← stinespringLeftMul0_adj]
    exact inner_self_nonneg
  have hd : 0 ≤ algebraMap ℝ A (‖c‖ ^ 2) - star c * c :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq c)
  have hkey := hpos _ hd
  have hexpand : stinespringPhi A H φ f (algebraMap ℝ A (‖c‖ ^ 2) - star c * c) f
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * ⟪f, f⟫_ℂ
        - ⟪stinespringLeftMul0 A H φ c f, stinespringLeftMul0 A H φ c f⟫_ℂ := by
    rw [stinespringPhi_sub, stinespringPhi_algebraMap]
    congr 1
    rw [← stinespringLeftMul0_inner, stinespringLeftMul0_mul]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← stinespringLeftMul0_adj]
  rw [hexpand, RCLike.re_to_complex, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hkey
  simp only [← RCLike.re_to_complex] at hkey
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ) f,
    ← norm_sq_eq_re_inner (𝕜 := ℂ) (stinespringLeftMul0 A H φ c f)] at hkey
  have hsq : ‖stinespringLeftMul0 A H φ c f‖ ^ 2 ≤ (‖c‖ * ‖f‖) ^ 2 := by
    rw [mul_pow]
    linarith [hkey]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq

-- N7b bounded version
private noncomputable def stinespringLeftMul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) : StinespringPre A H φ →L[ℂ] StinespringPre A H φ :=
  (stinespringLeftMul0 A H φ c).mkContinuous ‖c‖ (stinespringLeftMul0_bound A H φ c)

-- N9 K and rep
private abbrev stinespringK (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) := UniformSpace.Completion (StinespringPre A H φ)

private noncomputable def stinespringRep (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) : stinespringK A H φ →L[ℂ] stinespringK A H φ :=
  (stinespringLeftMul A H φ c).completion

private theorem stinespringLeftMul_apply (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) (f : StinespringPre A H φ) :
    (stinespringLeftMul A H φ c) f = stinespringLeftMul0 A H φ c f := rfl

-- N9 add
private theorem stinespringRep_add (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c d : A) :
    stinespringRep A H φ (c + d) = stinespringRep A H φ c + stinespringRep A H φ d := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih g =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe, add_apply,
      ← UniformSpace.Completion.coe_add, stinespringLeftMul_apply]
    apply completion_coe_eq_of_inner_eq
    intro w
    rw [stinespringLeftMul0_inner, stinespringPhi_add, ← stinespringLeftMul0_inner,
      ← stinespringLeftMul0_inner, ← inner_add_right]

-- N9 smul
private theorem stinespringRep_smul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (r : ℂ) (c : A) :
    stinespringRep A H φ (r • c) = r • stinespringRep A H φ c := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (stinespringRep A H φ (r • c)).continuous
      (ContinuousLinearMap.continuous _)
  | ih g =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe, smul_apply,
      ← UniformSpace.Completion.coe_smul, stinespringLeftMul_apply]
    apply completion_coe_eq_of_inner_eq
    intro w
    rw [stinespringLeftMul0_inner, stinespringPhi_smul, ← stinespringLeftMul0_inner,
      ← inner_smul_right]

private theorem stinespringRep_zero (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : stinespringRep A H φ 0 = 0 := by
  have h := stinespringRep_smul A H φ (0 : ℂ) (0 : A)
  simp only [smul_zero, zero_smul] at h
  exact h

-- N10 mul
private theorem stinespringRep_mul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c d : A) :
    stinespringRep A H φ (c * d) = stinespringRep A H φ c * stinespringRep A H φ d := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih g =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe, mul_apply_eq_comp,
      stinespringLeftMul_apply]
    rw [stinespringLeftMul0_mul]
    rfl

-- N10 one
private theorem stinespringRep_one (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : stinespringRep A H φ 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih g =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe,
      stinespringLeftMul_apply, stinespringLeftMul0_one, LinearMap.id_apply,
      one_apply_eq_self]

-- N10 star
private theorem stinespringRep_star (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) :
    stinespringRep A H φ (star c) = star (stinespringRep A H φ c) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    simp only [stinespringRep, ContinuousLinearMap.completion_apply_coe,
      stinespringLeftMul_apply, UniformSpace.Completion.inner_coe]
    rw [stinespringLeftMul0_adj, star_star]

-- N11 star algebra hom
private noncomputable def stinespringStarAlgHom (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : A →⋆ₐ[ℂ] (stinespringK A H φ →L[ℂ] stinespringK A H φ) where
  toFun := stinespringRep A H φ
  map_one' := stinespringRep_one A H φ
  map_mul' c d := stinespringRep_mul A H φ c d
  map_zero' := stinespringRep_zero A H φ
  map_add' c d := stinespringRep_add A H φ c d
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, stinespringRep_smul, stinespringRep_one]
  map_star' c := stinespringRep_star A H φ c

private theorem stinespringStarAlgHom_apply (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) :
    stinespringStarAlgHom A H φ c = stinespringRep A H φ c := rfl

-- N12 V0 and bound
private noncomputable def stinespringV0 (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : H →ₗ[ℂ] StinespringPre A H φ :=
  (StinespringPre.toPre A H φ).toLinearMap ∘ₗ Finsupp.lsingle 1

private theorem stinespringV0_apply (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (x : H) :
    stinespringV0 A H φ x = StinespringPre.toPre A H φ (Finsupp.single 1 x) := by
  simp only [stinespringV0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lsingle_apply]

private theorem stinespringV0_bound (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (x : H) :
    ‖stinespringV0 A H φ x‖ ≤ Real.sqrt ‖φ 1‖ * ‖x‖ := by
  have e1 : ‖stinespringV0 A H φ x‖ ^ 2 = RCLike.re ⟪x, φ 1 x⟫_ℂ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), stinespringV0_apply,
      stinespring_pre_inner_single, star_one, mul_one]
  have hle : RCLike.re ⟪x, φ 1 x⟫_ℂ ≤ ‖φ 1‖ * ‖x‖ ^ 2 := by
    calc RCLike.re ⟪x, φ 1 x⟫_ℂ ≤ ‖x‖ * ‖(φ 1) x‖ :=
          le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
      _ ≤ ‖x‖ * (‖φ 1‖ * ‖x‖) := by
          apply mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖φ 1‖ * ‖x‖ ^ 2 := by ring
  have h2 : ‖stinespringV0 A H φ x‖ ^ 2 ≤ ‖φ 1‖ * ‖x‖ ^ 2 := e1.symm ▸ hle
  have h3 : ‖stinespringV0 A H φ x‖ ^ 2 ≤ (Real.sqrt ‖φ 1‖ * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    exact h2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp h3

-- N12 V
private noncomputable def stinespringV (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) : H →L[ℂ] stinespringK A H φ :=
  UniformSpace.Completion.toComplL ∘L
    (stinespringV0 A H φ).mkContinuous (Real.sqrt ‖φ 1‖) (stinespringV0_bound A H φ)

private theorem stinespringV_apply (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (x : H) :
    stinespringV A H φ x
      = ((StinespringPre.toPre A H φ (Finsupp.single 1 x) :
        StinespringPre A H φ) : stinespringK A H φ) := by
  simp only [stinespringV, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearMap.mkContinuous_apply, stinespringV0_apply,
    UniformSpace.Completion.coe_toComplL]

-- N12 key identity
private theorem stinespringV_inner_rep (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (a : A) (x y : H) :
    ⟪stinespringV A H φ y, stinespringStarAlgHom A H φ a (stinespringV A H φ x)⟫_ℂ
      = ⟪y, φ a x⟫_ℂ := by
  simp only [stinespringV_apply, stinespringStarAlgHom_apply, stinespringRep,
    ContinuousLinearMap.completion_apply_coe, stinespringLeftMul_apply,
    stinespringLeftMul0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    StinespringPre.ofPre_toPre, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    UniformSpace.Completion.inner_coe, stinespring_pre_inner_def,
    stinespringForm_single]
  rw [star_one, one_mul, mul_one]

end MetaMathlibExt.Stinespring

namespace MathlibExt.Analysis.CStarAlgebra.StinespringWanted

/--
**Stinespring dilation theorem.** Let $A$ be a unital C*-algebra with its standard order, let $H$
be a complex Hilbert space, and let $\varphi : A \to B(H)$ be a completely positive map. Then
there are a complex Hilbert space $K$, a unital $*$-homomorphism $\pi : A \to B(K)$ and a bounded
linear map $V : H \to K$ such that $\varphi(a) = V^* \pi(a) V$ for every $a \in A$, where $V^*$
is the adjoint of $V$.

Proves `Wanted` entry `stinespring_dilation`.

Source: Stinespring dilation theorem, W. F. Stinespring, Proc. Amer. Math. Soc. 6 (1955); see
Paulsen, Completely Bounded Maps; Lean is general CP map A →CP B(H) dilation V† π(a) V, not
finite-dimensional Kraus form.
-/
theorem stinespring_dilation
    {A H : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
        (_ : CompleteSpace K) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      ∀ (a : A) (x : H), (φ a) x = (V†) ((π a) (V x)) := by
  refine ⟨MetaMathlibExt.Stinespring.stinespringK A H φ, inferInstance, inferInstance,
    inferInstance, MetaMathlibExt.Stinespring.stinespringStarAlgHom A H φ,
    MetaMathlibExt.Stinespring.stinespringV A H φ, ?_⟩
  intro a x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (MetaMathlibExt.Stinespring.stinespringV_inner_rep A H φ a x y).symm

end MathlibExt.Analysis.CStarAlgebra.StinespringWanted
end
