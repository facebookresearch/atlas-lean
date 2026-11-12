/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingDiagonalReflectionGeometry
import Code.FrontierB.FreeEvenHomogeneity
import Code.Ising.IsingFKGLayer
import Code.Ising.FiniteVolumeRelabel

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section Domain

variable (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)

def isingDiagonalDomainPlane (x : freeDomainVertices K) : Prop :=
  x.1 i - x.1 j = c

def isingDiagonalDomainLower (x : freeDomainVertices K) : Prop :=
  x.1 i - x.1 j < c

instance (x : freeDomainVertices K) :
    Decidable (isingDiagonalDomainPlane K i j c x) := by
  unfold isingDiagonalDomainPlane
  infer_instance

instance (x : freeDomainVertices K) :
    Decidable (isingDiagonalDomainLower K i j c x) := by
  unfold isingDiagonalDomainLower
  infer_instance

abbrev IsingDiagonalDomainPlane :=
  {x : freeDomainVertices K // isingDiagonalDomainPlane K i j c x}

abbrev IsingDiagonalDomainLower :=
  {x : freeDomainVertices K // isingDiagonalDomainLower K i j c x}

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)

def isingDiagonalDomainReflectEquiv :
    freeDomainVertices K ≃ freeDomainVertices K where
  toFun x := ⟨isingDiagonalReflect i j c x.1, (hK x.1).1 x.2⟩
  invFun x := ⟨isingDiagonalReflect i j c x.1, (hK x.1).1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact isingDiagonalReflect_involutive i j hij c x.1
  right_inv x := by
    apply Subtype.ext
    exact isingDiagonalReflect_involutive i j hij c x.1

@[simp] theorem isingDiagonalDomainReflectEquiv_val
    (x : freeDomainVertices K) :
    (isingDiagonalDomainReflectEquiv K i j hij c hK x).1 =
      isingDiagonalReflect i j c x.1 := rfl

theorem isingDiagonalDomainReflectEquiv_adj
    (x y : freeDomainVertices K) :
    (freeDomainGraph K).Adj x y ↔
      (freeDomainGraph K).Adj
        (isingDiagonalDomainReflectEquiv K i j hij c hK x)
        (isingDiagonalDomainReflectEquiv K i j hij c hK y) := by
  exact hypercubicLattice_adj_diagonalReflect i j hij c x.1 y.1

theorem isingDiagonalDomainReflect_fixed
    {x : freeDomainVertices K}
    (hx : isingDiagonalDomainPlane K i j c x) :
    isingDiagonalDomainReflectEquiv K i j hij c hK x = x := by
  apply Subtype.ext
  exact isingDiagonalReflect_fixed i j hij c x.1 hx

theorem isingDiagonalDomainReflect_lower_of_upper
    {x : freeDomainVertices K}
    (hp : ¬ isingDiagonalDomainPlane K i j c x)
    (hl : ¬ isingDiagonalDomainLower K i j c x) :
    isingDiagonalDomainLower K i j c
      (isingDiagonalDomainReflectEquiv K i j hij c hK x) := by
  unfold isingDiagonalDomainPlane at hp
  unfold isingDiagonalDomainLower at hl ⊢
  rw [isingDiagonalDomainReflectEquiv_val,
    isingDiagonalReflect_difference i j hij]
  omega

theorem isingDiagonalDomainReflect_not_plane
    {x : freeDomainVertices K}
    (hp : ¬ isingDiagonalDomainPlane K i j c x) :
    ¬ isingDiagonalDomainPlane K i j c
      (isingDiagonalDomainReflectEquiv K i j hij c hK x) := by
  intro hr
  apply hp
  unfold isingDiagonalDomainPlane at hr ⊢
  rw [isingDiagonalDomainReflectEquiv_val,
    isingDiagonalReflect_difference i j hij] at hr
  omega

theorem isingDiagonalDomainReflect_not_lower_of_lower
    {x : freeDomainVertices K}
    (hl : isingDiagonalDomainLower K i j c x) :
    ¬ isingDiagonalDomainLower K i j c
      (isingDiagonalDomainReflectEquiv K i j hij c hK x) := by
  unfold isingDiagonalDomainLower at hl ⊢
  rw [isingDiagonalDomainReflectEquiv_val,
    isingDiagonalReflect_difference i j hij]
  omega


def isingDiagonalDomainGlue
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    ConfigSpace (freeDomainVertices K) :=
  fun x => if hp : isingDiagonalDomainPlane K i j c x then
      boundary ⟨x, hp⟩
    else if hl : isingDiagonalDomainLower K i j c x then
      lower ⟨x, hl⟩
    else upper ⟨isingDiagonalDomainReflectEquiv K i j hij c hK x,
      isingDiagonalDomainReflect_lower_of_upper K i j hij c hK hp hl⟩

def isingDiagonalDomainSplit
    (sigma : ConfigSpace (freeDomainVertices K)) :
    ConfigSpace (IsingDiagonalDomainPlane K i j c) ×
      (ConfigSpace (IsingDiagonalDomainLower K i j c) ×
        ConfigSpace (IsingDiagonalDomainLower K i j c)) :=
  (fun x => sigma x.1,
    (fun x => sigma x.1,
      fun x => sigma (isingDiagonalDomainReflectEquiv K i j hij c hK x.1)))

@[simp] theorem isingDiagonalDomainSplit_glue
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingDiagonalDomainSplit K i j hij c hK
        (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) =
      (boundary, (lower, upper)) := by
  apply Prod.ext
  · funext x
    simp [isingDiagonalDomainSplit, isingDiagonalDomainGlue, x.2]
  · apply Prod.ext
    · funext x
      have hp : ¬ isingDiagonalDomainPlane K i j c x.1 := by
        exact ne_of_lt x.2
      simp [isingDiagonalDomainSplit, isingDiagonalDomainGlue, hp, x.2]
    · funext x
      have hp : ¬ isingDiagonalDomainPlane K i j c x.1 := by
        exact ne_of_lt x.2
      have hpR := isingDiagonalDomainReflect_not_plane K i j hij c hK hp
      have hlR := isingDiagonalDomainReflect_not_lower_of_lower
        K i j hij c hK x.2
      have hRR : isingDiagonalDomainReflectEquiv K i j hij c hK
          (isingDiagonalDomainReflectEquiv K i j hij c hK x.1) = x.1 :=
        (isingDiagonalDomainReflectEquiv K i j hij c hK).left_inv x.1
      simp [isingDiagonalDomainSplit, isingDiagonalDomainGlue, hpR, hlR, hRR]

@[simp] theorem isingDiagonalDomainGlue_split
    (sigma : ConfigSpace (freeDomainVertices K)) :
    isingDiagonalDomainGlue K i j hij c hK
        (isingDiagonalDomainSplit K i j hij c hK sigma).1
        (isingDiagonalDomainSplit K i j hij c hK sigma).2.1
        (isingDiagonalDomainSplit K i j hij c hK sigma).2.2 = sigma := by
  funext x
  by_cases hp : isingDiagonalDomainPlane K i j c x
  · have hfixed := isingDiagonalDomainReflect_fixed K i j hij c hK hp
    simp [isingDiagonalDomainGlue, isingDiagonalDomainSplit, hp, hfixed]
  · by_cases hl : isingDiagonalDomainLower K i j c x
    · simp [isingDiagonalDomainGlue, isingDiagonalDomainSplit, hp, hl]
    · have hRR : isingDiagonalDomainReflectEquiv K i j hij c hK
          (isingDiagonalDomainReflectEquiv K i j hij c hK x) = x :=
        (isingDiagonalDomainReflectEquiv K i j hij c hK).left_inv x
      simp [isingDiagonalDomainGlue, isingDiagonalDomainSplit, hp, hl, hRR]

def isingDiagonalDomainSplitEquiv :
    (ConfigSpace (IsingDiagonalDomainPlane K i j c) ×
      (ConfigSpace (IsingDiagonalDomainLower K i j c) ×
        ConfigSpace (IsingDiagonalDomainLower K i j c))) ≃
      ConfigSpace (freeDomainVertices K) where
  toFun p := isingDiagonalDomainGlue K i j hij c hK p.1 p.2.1 p.2.2
  invFun := isingDiagonalDomainSplit K i j hij c hK
  left_inv p := by rcases p with ⟨b, l, u⟩; simp
  right_inv := isingDiagonalDomainGlue_split K i j hij c hK

theorem isingDiagonalDomainGlue_reflect
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingCfgEquiv (isingDiagonalDomainReflectEquiv K i j hij c hK)
        (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) =
      isingDiagonalDomainGlue K i j hij c hK boundary upper lower := by
  funext x
  by_cases hp : isingDiagonalDomainPlane K i j c x
  · have hfixed := isingDiagonalDomainReflect_fixed K i j hij c hK hp
    simp [isingCfgEquiv, isingDiagonalDomainGlue, hp, hfixed]
  · by_cases hl : isingDiagonalDomainLower K i j c x
    · have hpR := isingDiagonalDomainReflect_not_plane K i j hij c hK hp
      have hlR := isingDiagonalDomainReflect_not_lower_of_lower
        K i j hij c hK hl
      have hRR : isingDiagonalDomainReflectEquiv K i j hij c hK
          (isingDiagonalDomainReflectEquiv K i j hij c hK x) = x :=
        (isingDiagonalDomainReflectEquiv K i j hij c hK).left_inv x
      simp [isingCfgEquiv, isingDiagonalDomainGlue, hp, hl, hpR, hlR, hRR]
    · have hlR := isingDiagonalDomainReflect_lower_of_upper
        K i j hij c hK hp hl
      have hpR := isingDiagonalDomainReflect_not_plane K i j hij c hK hp
      simp [isingCfgEquiv, isingDiagonalDomainGlue, hp, hl, hpR, hlR]

theorem isingDiagonalDomain_no_lower_upper_edge
    {x y : freeDomainVertices K}
    (hxy : (freeDomainGraph K).Adj x y) (hij0 : i ≠ j) :
    ¬ ((isingDiagonalDomainLower K i j c x ∧
          ¬ isingDiagonalDomainLower K i j c y ∧
          ¬ isingDiagonalDomainPlane K i j c y) ∨
        (isingDiagonalDomainLower K i j c y ∧
          ¬ isingDiagonalDomainLower K i j c x ∧
          ¬ isingDiagonalDomainPlane K i j c x)) := by
  rintro (⟨hxl, hyl, hyp⟩ | ⟨hyl, hxl, hxp⟩)
  · apply diagonalPlane_separates_adjacent i j hij0 c hxy hxl
    unfold isingDiagonalDomainLower at hyl
    unfold isingDiagonalDomainPlane at hyp
    omega
  · apply diagonalPlane_separates_adjacent i j hij0 c hxy.symm hyl
    unfold isingDiagonalDomainLower at hxl
    unfold isingDiagonalDomainPlane at hxp
    omega

private theorem isingDiagonalDomain_bond_four_identity
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c))
    (e : Sym2 (freeDomainVertices K))
    (he : e ∈ (freeDomainGraph K).edgeFinset) :
    bond (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) e +
        bond (isingDiagonalDomainGlue K i j hij c hK boundary upper lower) e =
      bond (isingDiagonalDomainGlue K i j hij c hK boundary lower lower) e +
        bond (isingDiagonalDomainGlue K i j hij c hK boundary upper upper) e := by
  induction e using Sym2.ind with
  | _ x y =>
      have hxy : (freeDomainGraph K).Adj x y := by
        rwa [SimpleGraph.mem_edgeFinset] at he
      have hn := isingDiagonalDomain_no_lower_upper_edge
        K i j c hxy hij
      simp only [bond_mk]
      by_cases hxp : isingDiagonalDomainPlane K i j c x
      · by_cases hyp : isingDiagonalDomainPlane K i j c y
        · simp [spin, isingDiagonalDomainGlue, hxp, hyp]
        · by_cases hyl : isingDiagonalDomainLower K i j c y
          · simp [spin, isingDiagonalDomainGlue, hxp, hyp, hyl]
          · simp [spin, isingDiagonalDomainGlue, hxp, hyp, hyl]
            ring
      · by_cases hxl : isingDiagonalDomainLower K i j c x
        · by_cases hyp : isingDiagonalDomainPlane K i j c y
          · simp [spin, isingDiagonalDomainGlue, hxp, hxl, hyp]
          · have hyl : isingDiagonalDomainLower K i j c y := by
              by_contra hyl
              exact hn (Or.inl ⟨hxl, hyl, hyp⟩)
            simp [spin, isingDiagonalDomainGlue, hxp, hxl, hyp, hyl]
        · by_cases hyp : isingDiagonalDomainPlane K i j c y
          · simp [spin, isingDiagonalDomainGlue, hxp, hxl, hyp]
            ring
          · have hyl : ¬ isingDiagonalDomainLower K i j c y := by
              intro hyl
              exact hn (Or.inr ⟨hyl, hxl, hxp⟩)
            simp [spin, isingDiagonalDomainGlue, hxp, hxl, hyp, hyl]
            ring

theorem isingDiagonalDomain_hamiltonian_midpoint
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    2 * hamiltonian (freeDomainGraph K) 0
        (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) =
      hamiltonian (freeDomainGraph K) 0
          (isingDiagonalDomainGlue K i j hij c hK boundary lower lower) +
        hamiltonian (freeDomainGraph K) 0
          (isingDiagonalDomainGlue K i j hij c hK boundary upper upper) := by
  let qlu := isingDiagonalDomainGlue K i j hij c hK boundary lower upper
  let qul := isingDiagonalDomainGlue K i j hij c hK boundary upper lower
  let qll := isingDiagonalDomainGlue K i j hij c hK boundary lower lower
  let quu := isingDiagonalDomainGlue K i j hij c hK boundary upper upper
  have hreflect : hamiltonian (freeDomainGraph K) 0 qlu =
      hamiltonian (freeDomainGraph K) 0 qul := by
    have h := hamiltonian_isingCfgEquiv (freeDomainGraph K) (freeDomainGraph K)
      (isingDiagonalDomainReflectEquiv K i j hij c hK)
      (isingDiagonalDomainReflectEquiv_adj K i j hij c hK) 0 qlu
    have hcfg := isingDiagonalDomainGlue_reflect
      K i j hij c hK boundary lower upper
    change isingCfgEquiv
        (isingDiagonalDomainReflectEquiv K i j hij c hK) qlu = qul at hcfg
    rw [hcfg] at h
    exact h.symm
  have hfour :
      (∑ e ∈ (freeDomainGraph K).edgeFinset, bond qlu e) +
          ∑ e ∈ (freeDomainGraph K).edgeFinset, bond qul e =
        (∑ e ∈ (freeDomainGraph K).edgeFinset, bond qll e) +
          ∑ e ∈ (freeDomainGraph K).edgeFinset, bond quu e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e he =>
      isingDiagonalDomain_bond_four_identity K i j hij c hK
        boundary lower upper e he
  unfold hamiltonian at hreflect ⊢
  simp only [zero_mul, sub_zero] at hreflect ⊢
  dsimp only [qlu, qul, qll, quu] at hfour hreflect ⊢
  linarith

noncomputable def isingDiagonalDomainHalfWeight
    (beta : Real)
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower : ConfigSpace (IsingDiagonalDomainLower K i j c)) : Real :=
  Real.exp (-(beta / 2) * hamiltonian (freeDomainGraph K) 0
    (isingDiagonalDomainGlue K i j hij c hK boundary lower lower))

theorem isingDiagonalDomainWeight_factor
    (beta : Real)
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingWeight (freeDomainGraph K) beta 0
        (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) =
      isingDiagonalDomainHalfWeight K i j hij c hK beta boundary lower *
        isingDiagonalDomainHalfWeight K i j hij c hK beta boundary upper := by
  unfold isingWeight isingDiagonalDomainHalfWeight
  rw [← Real.exp_add]
  congr 1
  have hmid := isingDiagonalDomain_hamiltonian_midpoint
    K i j hij c hK boundary lower upper
  linear_combination (-beta / 2) * hmid

theorem isingDiagonalDomainHalfWeight_pos
    (beta : Real)
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    0 < isingDiagonalDomainHalfWeight K i j hij c hK beta boundary lower :=
  Real.exp_pos _

private theorem isingDiagonalDomainGlue_self_sup
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingDiagonalDomainGlue K i j hij c hK boundary (lower ⊔ upper) (lower ⊔ upper) =
      isingDiagonalDomainGlue K i j hij c hK boundary lower lower ⊔
        isingDiagonalDomainGlue K i j hij c hK boundary upper upper := by
  funext x
  by_cases hp : isingDiagonalDomainPlane K i j c x
  · simp [isingDiagonalDomainGlue, hp]
  · by_cases hl : isingDiagonalDomainLower K i j c x
    · simp [isingDiagonalDomainGlue, hp, hl]
    · simp [isingDiagonalDomainGlue, hp, hl]

private theorem isingDiagonalDomainGlue_self_inf
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingDiagonalDomainGlue K i j hij c hK boundary (lower ⊓ upper) (lower ⊓ upper) =
      isingDiagonalDomainGlue K i j hij c hK boundary lower lower ⊓
        isingDiagonalDomainGlue K i j hij c hK boundary upper upper := by
  funext x
  by_cases hp : isingDiagonalDomainPlane K i j c x
  · simp [isingDiagonalDomainGlue, hp]
  · by_cases hl : isingDiagonalDomainLower K i j c x
    · simp [isingDiagonalDomainGlue, hp, hl]
    · simp [isingDiagonalDomainGlue, hp, hl]

theorem isingDiagonalDomainHalfWeight_fkg
    (beta : Real) (hbeta : 0 <= beta)
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c)) :
    FKGLatticeCondition
      (isingDiagonalDomainHalfWeight K i j hij c hK beta boundary) := by
  intro lower upper
  unfold isingDiagonalDomainHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsub := ifk_hamiltonian_submodular (freeDomainGraph K) 0
    (isingDiagonalDomainGlue K i j hij c hK boundary lower lower)
    (isingDiagonalDomainGlue K i j hij c hK boundary upper upper)
  rw [← isingDiagonalDomainGlue_self_sup K i j hij c hK,
    ← isingDiagonalDomainGlue_self_inf K i j hij c hK] at hsub
  nlinarith [mul_nonneg hbeta (sub_nonneg.mpr hsub)]



theorem isingDiagonalDomain_twoPoint_reflect_le
    (beta : Real) (hbeta : 0 <= beta)
    (x y : IsingDiagonalDomainLower K i j c) :
    isingExpectation (freeDomainGraph K) beta 0
        (fun sigma => spin sigma x.1 * spin sigma
          (isingDiagonalDomainReflectEquiv K i j hij c hK y.1)) <=
      isingExpectation (freeDomainGraph K) beta 0
        (fun sigma => spin sigma x.1 * spin sigma y.1) := by
  let w := isingDiagonalDomainHalfWeight K i j hij c hK beta
  let fx : ConfigSpace (IsingDiagonalDomainLower K i j c) -> Real :=
    fun sigma => spin sigma x
  let gy : ConfigSpace (IsingDiagonalDomainLower K i j c) -> Real :=
    fun sigma => spin sigma y
  have hfold := markovReflectionFold_sum_le w
    (fun b sigma => isingDiagonalDomainHalfWeight_pos
      K i j hij c hK beta b sigma)
    (fun b => isingDiagonalDomainHalfWeight_fkg
      K i j hij c hK beta hbeta b)
    fx gy
    (fun _ _ h => ifk_spin_mono h x)
    (fun _ _ h => ifk_spin_mono h y)
  have hcross :
      (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma x.1 * spin sigma
              (isingDiagonalDomainReflectEquiv K i j hij c hK y.1))) =
        ∑ b, ∑ l, ∑ u, (w b l * w b u) * (fx l * gy u) := by
    rw [← (isingDiagonalDomainSplitEquiv K i j hij c hK).bijective.sum_comp]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro u _
    change isingWeight (freeDomainGraph K) beta 0
        (isingDiagonalDomainGlue K i j hij c hK b l u) *
          (spin (isingDiagonalDomainGlue K i j hij c hK b l u) x.1 *
            spin (isingDiagonalDomainGlue K i j hij c hK b l u)
              (isingDiagonalDomainReflectEquiv K i j hij c hK y.1)) = _
    rw [isingDiagonalDomainWeight_factor]
    have hxp : ¬ isingDiagonalDomainPlane K i j c x.1 := ne_of_lt x.2
    have hyp : ¬ isingDiagonalDomainPlane K i j c y.1 := ne_of_lt y.2
    have hypR := isingDiagonalDomainReflect_not_plane K i j hij c hK hyp
    have hylR := isingDiagonalDomainReflect_not_lower_of_lower
      K i j hij c hK y.2
    have hRR : isingDiagonalDomainReflectEquiv K i j hij c hK
        (isingDiagonalDomainReflectEquiv K i j hij c hK y.1) = y.1 :=
      (isingDiagonalDomainReflectEquiv K i j hij c hK).left_inv y.1
    have hxspin : spin (isingDiagonalDomainGlue K i j hij c hK b l u) x.1 =
        spin l x := by
      simp [spin, isingDiagonalDomainGlue, hxp, x.2]
    have hyspin : spin (isingDiagonalDomainGlue K i j hij c hK b l u)
        (isingDiagonalDomainReflectEquiv K i j hij c hK y.1) = spin u y := by
      simp [spin, isingDiagonalDomainGlue, hypR, hylR, hRR]
    rw [hxspin, hyspin]
  have hsame :
      (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma x.1 * spin sigma y.1)) =
        ∑ b, ∑ l, ∑ u, (w b l * w b u) * (fx l * gy l) := by
    rw [← (isingDiagonalDomainSplitEquiv K i j hij c hK).bijective.sum_comp]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro u _
    change isingWeight (freeDomainGraph K) beta 0
        (isingDiagonalDomainGlue K i j hij c hK b l u) *
          (spin (isingDiagonalDomainGlue K i j hij c hK b l u) x.1 *
            spin (isingDiagonalDomainGlue K i j hij c hK b l u) y.1) = _
    rw [isingDiagonalDomainWeight_factor]
    have hxp : ¬ isingDiagonalDomainPlane K i j c x.1 := ne_of_lt x.2
    have hyp : ¬ isingDiagonalDomainPlane K i j c y.1 := ne_of_lt y.2
    have hxspin : spin (isingDiagonalDomainGlue K i j hij c hK b l u) x.1 =
        spin l x := by
      simp [spin, isingDiagonalDomainGlue, hxp, x.2]
    have hyspin : spin (isingDiagonalDomainGlue K i j hij c hK b l u) y.1 =
        spin l y := by
      simp [spin, isingDiagonalDomainGlue, hyp, y.2]
    rw [hxspin, hyspin]
  unfold isingExpectation isingProb
  let Z := isingZ (freeDomainGraph K) beta 0
  have hZ : 0 <= Z := (isingZ_pos (freeDomainGraph K) beta 0).le
  calc
    (∑ s, isingWeight (freeDomainGraph K) beta 0 s / Z *
        (spin s x.1 * spin s
          (isingDiagonalDomainReflectEquiv K i j hij c hK y.1))) =
      (∑ s, isingWeight (freeDomainGraph K) beta 0 s *
        (spin s x.1 * spin s
          (isingDiagonalDomainReflectEquiv K i j hij c hK y.1))) / Z := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
    _ <= (∑ s, isingWeight (freeDomainGraph K) beta 0 s *
        (spin s x.1 * spin s y.1)) / Z := by
      apply div_le_div_of_nonneg_right _ hZ
      rw [hcross, hsame]
      exact hfold
    _ = ∑ s, isingWeight (freeDomainGraph K) beta 0 s / Z *
        (spin s x.1 * spin s y.1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring

end Domain





noncomputable def isingDiagonalSymmetricHull
    (K : Finset (Site d)) (i j : Fin d) (c : Int) : Finset (Site d) :=
  K ∪ K.image (isingDiagonalReflect i j c)

theorem mem_isingDiagonalSymmetricHull_reflect_iff
    (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)
    (x : Site d) :
    x ∈ isingDiagonalSymmetricHull K i j c ↔
      isingDiagonalReflect i j c x ∈ isingDiagonalSymmetricHull K i j c := by
  classical
  constructor
  · intro hx
    rw [isingDiagonalSymmetricHull, Finset.mem_union] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      left
      rw [← hyx, isingDiagonalReflect_involutive i j hij]
      exact hy
  · intro hx
    have hr := (show isingDiagonalReflect i j c x ∈
        isingDiagonalSymmetricHull K i j c from hx)
    have := (show isingDiagonalReflect i j c
        (isingDiagonalReflect i j c x) ∈
          isingDiagonalSymmetricHull K i j c from
      (by
        rw [isingDiagonalSymmetricHull, Finset.mem_union]
        rw [isingDiagonalSymmetricHull, Finset.mem_union] at hr
        rcases hr with hr | hr
        · exact Or.inr (Finset.mem_image.mpr
            ⟨isingDiagonalReflect i j c x, hr, rfl⟩)
        · obtain ⟨y, hy, hyr⟩ := Finset.mem_image.mp hr
          left
          rw [← hyr, isingDiagonalReflect_involutive i j hij]
          exact hy))
    rwa [isingDiagonalReflect_involutive i j hij] at this

theorem subset_isingDiagonalSymmetricHull
    (K : Finset (Site d)) (i j : Fin d) (c : Int) :
    K ⊆ isingDiagonalSymmetricHull K i j c := by
  intro x hx
  exact Finset.mem_union_left _ hx



theorem freeDomain_spinProd_diagonalReflect_le
    (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)
    (hK : ∀ x : Site d,
      x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
    (beta : Real) (hbeta : 0 <= beta)
    (a b : Site d) (ha : a ∈ K) (hb : b ∈ K)
    (hal : a i - a j < c) (hbl : b i - b j < c)
    (hab : a ≠ b)
    (habR : a ≠ isingDiagonalReflect i j c b) :
    isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K
          {a, isingDiagonalReflect i j c b})) <=
      isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K {a, b})) := by
  let aK : freeDomainVertices K := ⟨a, ha⟩
  let bK : freeDomainVertices K := ⟨b, hb⟩
  let aL : IsingDiagonalDomainLower K i j c := ⟨aK, hal⟩
  let bL : IsingDiagonalDomainLower K i j c := ⟨bK, hbl⟩
  have hfold := isingDiagonalDomain_twoPoint_reflect_le
    K i j hij c hK beta hbeta aL bL
  have hfar : freeDomainSpinSupport K
      {a, isingDiagonalReflect i j c b} =
      {aK, isingDiagonalDomainReflectEquiv K i j hij c hK bK} := by
    ext z
    simp only [freeDomainSpinSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hz | hz)
      · left
        apply Subtype.ext
        exact hz
      · right
        apply Subtype.ext
        exact hz
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hnear : freeDomainSpinSupport K {a, b} = {aK, bK} := by
    ext z
    simp only [freeDomainSpinSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hz | hz)
      · left
        apply Subtype.ext
        exact hz
      · right
        apply Subtype.ext
        exact hz
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hnearNe : aK ≠ bK := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hfarNe : aK ≠ isingDiagonalDomainReflectEquiv K i j hij c hK bK := by
    intro h
    exact habR (congrArg Subtype.val h)
  rw [hfar, hnear]
  have hfarProd : spinProd
      ({aK, isingDiagonalDomainReflectEquiv K i j hij c hK bK} :
        Finset (freeDomainVertices K)) =
      fun sigma => spin sigma aK *
        spin sigma (isingDiagonalDomainReflectEquiv K i j hij c hK bK) := by
    funext sigma
    rw [spinProd, Finset.prod_pair hfarNe]
  have hnearProd : spinProd ({aK, bK} : Finset (freeDomainVertices K)) =
      fun sigma => spin sigma aK * spin sigma bK := by
    funext sigma
    rw [spinProd, Finset.prod_pair hnearNe]
  rw [hfarProd, hnearProd]
  simpa [aL, bL] using hfold

end StatMech.FrontierA
