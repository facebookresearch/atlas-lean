/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingCoordinateReflectionDomain
import Code.FrontierA.IsingTorusSpinReflection

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)
variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)



noncomputable def isingCoordinateDomainCrossBoundary :
    Finset (IsingCoordinateDomainLower K i m) :=
  Finset.univ.filter fun z =>
    (freeDomainGraph K).Adj z.1
      (isingCoordinateDomainReflectEquiv K i m hK z.1)

def isingCoordinateDomainCrossEdge
    (z : IsingCoordinateDomainLower K i m) :
    Sym2 (freeDomainVertices K) :=
  s(z.1, isingCoordinateDomainReflectEquiv K i m hK z.1)

theorem isingCoordinateDomainCrossEdge_mem
    {z : IsingCoordinateDomainLower K i m}
    (hz : z ∈ isingCoordinateDomainCrossBoundary K i m hK) :
    isingCoordinateDomainCrossEdge K i m hK z ∈
      (freeDomainGraph K).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  simpa [isingCoordinateDomainCrossBoundary,
    isingCoordinateDomainCrossEdge] using hz

theorem isingCoordinateDomainCrossEdge_injective :
    Function.Injective (isingCoordinateDomainCrossEdge K i m hK) := by
  intro z w hzw
  rw [isingCoordinateDomainCrossEdge, isingCoordinateDomainCrossEdge,
    Sym2.eq_iff] at hzw
  rcases hzw with hzw | hswap
  · exact Subtype.ext hzw.1
  · exfalso
    have hzlower := z.2
    have hwupper := isingCoordinateDomainReflect_not_lower_of_lower
      K i m hK w.2
    apply hwupper
    rw [← hswap.1]
    exact hzlower

private theorem isingCoordinateDomainGlue_cross_spin_lower
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m))
    (z : IsingCoordinateDomainLower K i m) :
    spin (isingCoordinateDomainGlue K i m hK boundary lower upper) z.1 =
      spin lower z := by
  have hp : ¬ isingCoordinateDomainPlane K i m z.1 := by
    have hl := z.2
    unfold isingCoordinateDomainPlane isingCoordinatePlane
    unfold isingCoordinateDomainLower isingCoordinateLower at hl
    omega
  simp [spin, isingCoordinateDomainGlue, hp, z.2]

private theorem isingCoordinateDomainGlue_cross_spin_upper
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m))
    (z : IsingCoordinateDomainLower K i m) :
    spin (isingCoordinateDomainGlue K i m hK boundary lower upper)
        (isingCoordinateDomainReflectEquiv K i m hK z.1) =
      spin upper z := by
  have hp : ¬ isingCoordinateDomainPlane K i m z.1 := by
    have hl := z.2
    unfold isingCoordinateDomainPlane isingCoordinatePlane
    unfold isingCoordinateDomainLower isingCoordinateLower at hl
    omega
  have hpR := isingCoordinateDomainReflect_not_plane K i m hK hp
  have hlR := isingCoordinateDomainReflect_not_lower_of_lower
    K i m hK z.2
  have hRR : isingCoordinateDomainReflectEquiv K i m hK
      (isingCoordinateDomainReflectEquiv K i m hK z.1) = z.1 :=
    (isingCoordinateDomainReflectEquiv K i m hK).left_inv z.1
  simp [spin, isingCoordinateDomainGlue, hpR, hlR, hRR]

@[simp] private theorem isingCoordinateDomainGlue_spin_plane
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m))
    {x : freeDomainVertices K}
    (hp : isingCoordinateDomainPlane K i m x) :
    spin (isingCoordinateDomainGlue K i m hK boundary lower upper) x =
      spin boundary ⟨x, hp⟩ := by
  simp [spin, isingCoordinateDomainGlue, hp]

@[simp] private theorem isingCoordinateDomainGlue_spin_lower
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m))
    {x : freeDomainVertices K}
    (hp : ¬ isingCoordinateDomainPlane K i m x)
    (hl : isingCoordinateDomainLower K i m x) :
    spin (isingCoordinateDomainGlue K i m hK boundary lower upper) x =
      spin lower ⟨x, hl⟩ := by
  simp [spin, isingCoordinateDomainGlue, hp, hl]

@[simp] private theorem isingCoordinateDomainGlue_spin_upper
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m))
    {x : freeDomainVertices K}
    (hp : ¬ isingCoordinateDomainPlane K i m x)
    (hl : ¬ isingCoordinateDomainLower K i m x) :
    spin (isingCoordinateDomainGlue K i m hK boundary lower upper) x =
      spin upper ⟨isingCoordinateDomainReflectEquiv K i m hK x,
        isingCoordinateDomainReflect_lower_of_upper K i m hK hp hl⟩ := by
  simp [spin, isingCoordinateDomainGlue, hp, hl]

private theorem isingCoordinateDomain_bond_correction_zero_of_not_cross
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m))
    (e : Sym2 (freeDomainVertices K))
    (he : e ∈ (freeDomainGraph K).edgeFinset)
    (hcross : e ∉
      (isingCoordinateDomainCrossBoundary K i m hK).image
        (isingCoordinateDomainCrossEdge K i m hK)) :
    bond (isingCoordinateDomainGlue K i m hK boundary lower lower) e +
        bond (isingCoordinateDomainGlue K i m hK boundary upper upper) e -
        bond (isingCoordinateDomainGlue K i m hK boundary lower upper) e -
        bond (isingCoordinateDomainGlue K i m hK boundary upper lower) e = 0 := by
  induction e using Sym2.ind with
  | _ x y =>
      have hxy : (freeDomainGraph K).Adj x y := by
        rwa [SimpleGraph.mem_edgeFinset] at he
      simp only [bond_mk]
      by_cases hxp : isingCoordinateDomainPlane K i m x
      · by_cases hyp : isingCoordinateDomainPlane K i m y
        · rw [isingCoordinateDomainGlue_spin_plane K i m hK boundary lower lower hxp,
            isingCoordinateDomainGlue_spin_plane K i m hK boundary lower lower hyp,
            isingCoordinateDomainGlue_spin_plane K i m hK boundary upper upper hxp,
            isingCoordinateDomainGlue_spin_plane K i m hK boundary upper upper hyp,
            isingCoordinateDomainGlue_spin_plane K i m hK boundary lower upper hxp,
            isingCoordinateDomainGlue_spin_plane K i m hK boundary lower upper hyp,
            isingCoordinateDomainGlue_spin_plane K i m hK boundary upper lower hxp,
            isingCoordinateDomainGlue_spin_plane K i m hK boundary upper lower hyp]
          ring
        · by_cases hyl : isingCoordinateDomainLower K i m y
          · rw [isingCoordinateDomainGlue_spin_plane K i m hK boundary lower lower hxp,
              isingCoordinateDomainGlue_spin_lower K i m hK boundary lower lower hyp hyl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary upper upper hxp,
              isingCoordinateDomainGlue_spin_lower K i m hK boundary upper upper hyp hyl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary lower upper hxp,
              isingCoordinateDomainGlue_spin_lower K i m hK boundary lower upper hyp hyl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary upper lower hxp,
              isingCoordinateDomainGlue_spin_lower K i m hK boundary upper lower hyp hyl]
            ring
          · rw [isingCoordinateDomainGlue_spin_plane K i m hK boundary lower lower hxp,
              isingCoordinateDomainGlue_spin_upper K i m hK boundary lower lower hyp hyl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary upper upper hxp,
              isingCoordinateDomainGlue_spin_upper K i m hK boundary upper upper hyp hyl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary lower upper hxp,
              isingCoordinateDomainGlue_spin_upper K i m hK boundary lower upper hyp hyl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary upper lower hxp,
              isingCoordinateDomainGlue_spin_upper K i m hK boundary upper lower hyp hyl]
            ring
      · by_cases hxl : isingCoordinateDomainLower K i m x
        · by_cases hyp : isingCoordinateDomainPlane K i m y
          · rw [isingCoordinateDomainGlue_spin_lower K i m hK boundary lower lower hxp hxl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary lower lower hyp,
              isingCoordinateDomainGlue_spin_lower K i m hK boundary upper upper hxp hxl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary upper upper hyp,
              isingCoordinateDomainGlue_spin_lower K i m hK boundary lower upper hxp hxl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary lower upper hyp,
              isingCoordinateDomainGlue_spin_lower K i m hK boundary upper lower hxp hxl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary upper lower hyp]
            ring
          · by_cases hyl : isingCoordinateDomainLower K i m y
            · rw [isingCoordinateDomainGlue_spin_lower K i m hK boundary lower lower hxp hxl,
                isingCoordinateDomainGlue_spin_lower K i m hK boundary lower lower hyp hyl,
                isingCoordinateDomainGlue_spin_lower K i m hK boundary upper upper hxp hxl,
                isingCoordinateDomainGlue_spin_lower K i m hK boundary upper upper hyp hyl,
                isingCoordinateDomainGlue_spin_lower K i m hK boundary lower upper hxp hxl,
                isingCoordinateDomainGlue_spin_lower K i m hK boundary lower upper hyp hyl,
                isingCoordinateDomainGlue_spin_lower K i m hK boundary upper lower hxp hxl,
                isingCoordinateDomainGlue_spin_lower K i m hK boundary upper lower hyp hyl]
              ring
            · have hreflect : isingCoordinateDomainReflectEquiv K i m hK x = y := by
                apply Subtype.ext
                exact coordinateReflect_eq_of_adj_crossing i m hxy hxl hyp hyl
              exfalso
              apply hcross
              rw [Finset.mem_image]
              let z : IsingCoordinateDomainLower K i m := ⟨x, hxl⟩
              refine ⟨z, ?_, ?_⟩
              · simp only [isingCoordinateDomainCrossBoundary,
                    Finset.mem_filter, Finset.mem_univ, true_and]
                simpa [z, hreflect] using hxy
              · simp [isingCoordinateDomainCrossEdge, z, hreflect]
        · by_cases hyp : isingCoordinateDomainPlane K i m y
          · rw [isingCoordinateDomainGlue_spin_upper K i m hK boundary lower lower hxp hxl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary lower lower hyp,
              isingCoordinateDomainGlue_spin_upper K i m hK boundary upper upper hxp hxl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary upper upper hyp,
              isingCoordinateDomainGlue_spin_upper K i m hK boundary lower upper hxp hxl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary lower upper hyp,
              isingCoordinateDomainGlue_spin_upper K i m hK boundary upper lower hxp hxl,
              isingCoordinateDomainGlue_spin_plane K i m hK boundary upper lower hyp]
            ring
          · by_cases hyl : isingCoordinateDomainLower K i m y
            · have hreflect : isingCoordinateDomainReflectEquiv K i m hK y = x := by
                apply Subtype.ext
                exact coordinateReflect_eq_of_adj_crossing_symm
                  i m hxy hyl hxp hxl
              exfalso
              apply hcross
              rw [Finset.mem_image]
              let z : IsingCoordinateDomainLower K i m := ⟨y, hyl⟩
              refine ⟨z, ?_, ?_⟩
              · simp only [isingCoordinateDomainCrossBoundary,
                    Finset.mem_filter, Finset.mem_univ, true_and]
                simpa [z, hreflect] using hxy.symm
              · simp [isingCoordinateDomainCrossEdge, z, hreflect,
                  Sym2.eq_iff]
            · rw [isingCoordinateDomainGlue_spin_upper K i m hK boundary lower lower hxp hxl,
                isingCoordinateDomainGlue_spin_upper K i m hK boundary lower lower hyp hyl,
                isingCoordinateDomainGlue_spin_upper K i m hK boundary upper upper hxp hxl,
                isingCoordinateDomainGlue_spin_upper K i m hK boundary upper upper hyp hyl,
                isingCoordinateDomainGlue_spin_upper K i m hK boundary lower upper hxp hxl,
                isingCoordinateDomainGlue_spin_upper K i m hK boundary lower upper hyp hyl,
                isingCoordinateDomainGlue_spin_upper K i m hK boundary upper lower hxp hxl,
                isingCoordinateDomainGlue_spin_upper K i m hK boundary upper lower hyp hyl]
              ring

private theorem isingCoordinateDomain_bond_correction_cross
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m))
    (z : IsingCoordinateDomainLower K i m) :
    bond (isingCoordinateDomainGlue K i m hK boundary lower lower)
          (isingCoordinateDomainCrossEdge K i m hK z) +
        bond (isingCoordinateDomainGlue K i m hK boundary upper upper)
          (isingCoordinateDomainCrossEdge K i m hK z) -
        bond (isingCoordinateDomainGlue K i m hK boundary lower upper)
          (isingCoordinateDomainCrossEdge K i m hK z) -
        bond (isingCoordinateDomainGlue K i m hK boundary upper lower)
          (isingCoordinateDomainCrossEdge K i m hK z) =
      2 * (1 - spin lower z * spin upper z) := by
  rw [isingCoordinateDomainCrossEdge]
  simp only [bond_mk]
  rw [isingCoordinateDomainGlue_cross_spin_lower K i m hK boundary lower lower z,
    isingCoordinateDomainGlue_cross_spin_upper K i m hK boundary lower lower z,
    isingCoordinateDomainGlue_cross_spin_lower K i m hK boundary upper upper z,
    isingCoordinateDomainGlue_cross_spin_upper K i m hK boundary upper upper z,
    isingCoordinateDomainGlue_cross_spin_lower K i m hK boundary lower upper z,
    isingCoordinateDomainGlue_cross_spin_upper K i m hK boundary lower upper z,
    isingCoordinateDomainGlue_cross_spin_lower K i m hK boundary upper lower z,
    isingCoordinateDomainGlue_cross_spin_upper K i m hK boundary upper lower z]
  have hl := spin_sq lower z
  have hu := spin_sq upper z
  nlinarith


theorem isingCoordinateDomain_hamiltonian_cross_correction
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    2 * hamiltonian (freeDomainGraph K) 0
        (isingCoordinateDomainGlue K i m hK boundary lower upper) =
      hamiltonian (freeDomainGraph K) 0
          (isingCoordinateDomainGlue K i m hK boundary lower lower) +
        hamiltonian (freeDomainGraph K) 0
          (isingCoordinateDomainGlue K i m hK boundary upper upper) +
        2 * ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
          (1 - spin lower z * spin upper z) := by
  let C := (isingCoordinateDomainCrossBoundary K i m hK).image
    (isingCoordinateDomainCrossEdge K i m hK)
  let qlu := isingCoordinateDomainGlue K i m hK boundary lower upper
  let qul := isingCoordinateDomainGlue K i m hK boundary upper lower
  let qll := isingCoordinateDomainGlue K i m hK boundary lower lower
  let quu := isingCoordinateDomainGlue K i m hK boundary upper upper
  have hCsub : C ⊆ (freeDomainGraph K).edgeFinset := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    exact isingCoordinateDomainCrossEdge_mem K i m hK hz
  have hdecomp (f : Sym2 (freeDomainVertices K) → Real) :
      ∑ e ∈ (freeDomainGraph K).edgeFinset, f e =
        (∑ e ∈ C, f e) +
          ∑ e ∈ (freeDomainGraph K).edgeFinset \ C, f e := by
    rw [← Finset.sum_union Finset.disjoint_sdiff]
    congr 2
    exact (Finset.union_sdiff_of_subset hCsub).symm
  let corr : Sym2 (freeDomainVertices K) → Real := fun e =>
    bond qll e + bond quu e - bond qlu e - bond qul e
  have hcrossSum : (∑ e ∈ C, corr e) =
      2 * ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
        (1 - spin lower z * spin upper z) := by
    dsimp [C]
    rw [Finset.sum_image (Set.injOn_of_injective
      (isingCoordinateDomainCrossEdge_injective K i m hK))]
    calc
      (∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
          corr (isingCoordinateDomainCrossEdge K i m hK z)) =
          ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
            2 * (1 - spin lower z * spin upper z) := by
        apply Finset.sum_congr rfl
        intro z _
        exact isingCoordinateDomain_bond_correction_cross
          K i m hK boundary lower upper z
      _ = 2 * ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
          (1 - spin lower z * spin upper z) := by
        rw [Finset.mul_sum]
  have hnoncross :
      (∑ e ∈ (freeDomainGraph K).edgeFinset \ C, corr e) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    exact isingCoordinateDomain_bond_correction_zero_of_not_cross
      K i m hK boundary lower upper e (Finset.mem_sdiff.mp he).1
        (Finset.mem_sdiff.mp he).2
  have hreflectH :
      hamiltonian (freeDomainGraph K) 0 qlu =
        hamiltonian (freeDomainGraph K) 0 qul := by
    have h := hamiltonian_isingCfgEquiv
      (freeDomainGraph K) (freeDomainGraph K)
      (isingCoordinateDomainReflectEquiv K i m hK)
      (isingCoordinateDomainReflectEquiv_adj K i m hK) 0 qlu
    have hcfg := isingCoordinateDomainGlue_reflect
      K i m hK boundary lower upper
    change isingCfgEquiv (isingCoordinateDomainReflectEquiv K i m hK) qlu =
      qul at hcfg
    rw [hcfg] at h
    exact h.symm
  have hreflectBond :
      (∑ e ∈ (freeDomainGraph K).edgeFinset, bond qlu e) =
        ∑ e ∈ (freeDomainGraph K).edgeFinset, bond qul e := by
    unfold hamiltonian at hreflectH
    simp only [zero_mul, sub_zero] at hreflectH
    linarith
  have hsum := hdecomp corr
  rw [hcrossSum, hnoncross, add_zero] at hsum
  have hsum' :
      (∑ e ∈ (freeDomainGraph K).edgeFinset,
          bond (isingCoordinateDomainGlue K i m hK boundary lower lower) e) +
        (∑ e ∈ (freeDomainGraph K).edgeFinset,
          bond (isingCoordinateDomainGlue K i m hK boundary upper upper) e) -
        2 * (∑ e ∈ (freeDomainGraph K).edgeFinset,
          bond (isingCoordinateDomainGlue K i m hK boundary lower upper) e) =
        2 * ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
          (1 - spin lower z * spin upper z) := by
    calc
      _ = Finset.sum (freeDomainGraph K).edgeFinset (fun e =>
          bond qll e + bond quu e - bond qlu e - bond qul e) := by
        dsimp only [qll, quu, qlu, qul]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, hreflectBond]
        ring
      _ = Finset.sum (freeDomainGraph K).edgeFinset corr := by
        rfl
      _ = _ := hsum
  unfold hamiltonian at ⊢
  simp only [zero_mul, sub_zero]
  linear_combination hsum'

noncomputable def isingCoordinateDomainHalfWeight
    (beta : Real)
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower : ConfigSpace (IsingCoordinateDomainLower K i m)) : Real :=
  Real.exp (-(beta / 2) * hamiltonian (freeDomainGraph K) 0
    (isingCoordinateDomainGlue K i m hK boundary lower lower))

theorem isingCoordinateDomainWeight_factor
    (beta : Real)
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    isingWeight (freeDomainGraph K) beta 0
        (isingCoordinateDomainGlue K i m hK boundary lower upper) =
      isingCoordinateDomainHalfWeight K i m hK beta boundary lower *
        isingCoordinateDomainHalfWeight K i m hK beta boundary upper *
        Real.exp (-beta *
          (isingCoordinateDomainCrossBoundary K i m hK).card) *
        Real.exp (beta * ∑ z ∈
          isingCoordinateDomainCrossBoundary K i m hK,
            spin lower z * spin upper z) := by
  unfold isingWeight isingCoordinateDomainHalfWeight
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hcorr := isingCoordinateDomain_hamiltonian_cross_correction
    K i m hK boundary lower upper
  have hsplit :
      (∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
        (1 - spin lower z * spin upper z)) =
      ((isingCoordinateDomainCrossBoundary K i m hK).card : Real) -
        ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
          spin lower z * spin upper z := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hsplit] at hcorr
  linear_combination (-beta / 2) * hcorr

end

end StatMech.FrontierA
