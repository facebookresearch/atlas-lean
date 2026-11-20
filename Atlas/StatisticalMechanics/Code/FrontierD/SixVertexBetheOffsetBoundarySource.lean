/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetFiniteResidual









namespace StatMech.FrontierD

open Finset

noncomputable section


def sixVertexEvenChargeLeftBoundaryIndex (s k : Nat) (i : Fin s) :
    Fin (((2 * s + k + 1) + (2 * s + k + 1))) :=
  ⟨i, by omega⟩


def sixVertexEvenChargeRightBoundaryIndex (s k : Nat) (i : Fin s) :
    Fin (((2 * s + k + 1) + (2 * s + k + 1))) :=
  ⟨s + sixVertexFixedChargeBetheParticleCount (2 * s) k + i, by
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    omega⟩



theorem sixVertexEvenChargeOffsetBoundarySource_eq_boundarySums
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexEvenChargeOffsetBoundarySource hc s k j =
      (∑ i : Fin s, sixVertexTheta c
        (sixVertexEvenChargeAlignedHalfRoots hc s k j)
        (sixVertexHalfFilledBetheRoots hc (2 * s + k)
          (sixVertexEvenChargeLeftBoundaryIndex s k i))) +
      ∑ i : Fin s, sixVertexTheta c
        (sixVertexEvenChargeAlignedHalfRoots hc s k j)
        (sixVertexHalfFilledBetheRoots hc (2 * s + k)
          (sixVertexEvenChargeRightBoundaryIndex s k i)) := by
  let n := sixVertexFixedChargeBetheParticleCount (2 * s) k
  let H := (2 * s + k + 1) + (2 * s + k + 1)
  let f : Fin H → Real := fun l => sixVertexTheta c
    (sixVertexEvenChargeAlignedHalfRoots hc s k j)
    (sixVertexHalfFilledBetheRoots hc (2 * s + k) l)
  have hH : H = s + n + s := by
    dsimp [H, n]
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    omega
  have hH' : H = s + (n + s) := by omega
  have htotal : (∑ l : Fin H, f l) =
      (∑ i : Fin s, f ⟨i, by omega⟩) +
      ((∑ l : Fin n, f ⟨s + l, by omega⟩) +
      ∑ i : Fin s, f ⟨s + n + i, by omega⟩) := by
    let g : Fin (s + (n + s)) → Real := fun i => f (Fin.cast hH'.symm i)
    have hfirst := Fin.sum_univ_add (a := s) (b := n + s) g
    have hsecond := Fin.sum_univ_add (a := n) (b := s)
      (fun i : Fin (n + s) => g (Fin.natAdd s i))
    rw [hsecond] at hfirst
    let e : Fin (s + (n + s)) ≃ Fin H :=
      (Fin.castOrderIso hH'.symm).toEquiv
    have hleft : (∑ i : Fin s, g (Fin.castAdd (n + s) i)) =
        ∑ i : Fin s, f ⟨i, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [g, e]
      congr 1
    have hmiddle :
        (∑ l : Fin n, g (Fin.natAdd s (Fin.castAdd s l))) =
        ∑ l : Fin n, f ⟨s + l, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [g, e]
      congr 1
    have hright : (∑ i : Fin s, g (Fin.natAdd s (Fin.natAdd n i))) =
        ∑ i : Fin s, f ⟨s + n + i, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [g, e]
      congr 1
      apply Fin.ext
      simp only [Fin.cast, Fin.natAdd, Fin.val_mk]
      omega
    calc
      (∑ l : Fin H, f l) = ∑ i : Fin (s + (n + s)), g i := by
        exact (Equiv.sum_comp e f).symm
      _ = (∑ i : Fin s, g (Fin.castAdd (n + s) i)) +
          ((∑ l : Fin n, g (Fin.natAdd s (Fin.castAdd s l))) +
          ∑ i : Fin s, g (Fin.natAdd s (Fin.natAdd n i))) := hfirst
      _ = _ := by rw [hleft, hmiddle, hright]
  unfold sixVertexEvenChargeOffsetBoundarySource
  have haligned :
      (∑ l, sixVertexTheta c
        (sixVertexEvenChargeAlignedHalfRoots hc s k j)
        (sixVertexEvenChargeAlignedHalfRoots hc s k l)) =
      ∑ l : Fin n, f ⟨s + l, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro l _
    simp only [f, sixVertexEvenChargeAlignedHalfRoots,
      sixVertexEvenChargeHalfIndex]
    congr 2
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  rw [haligned]
  change (∑ l : Fin H, f l) -
      ∑ l : Fin n, f ⟨s + l, by omega⟩ = _
  rw [htotal]
  dsimp only [f, H, n, sixVertexEvenChargeAlignedHalfRoots,
    sixVertexEvenChargeHalfIndex, sixVertexEvenChargeLeftBoundaryIndex,
    sixVertexEvenChargeRightBoundaryIndex]
  ring

end

end StatMech.FrontierD
