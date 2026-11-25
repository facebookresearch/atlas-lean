/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleMixedFace

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber

namespace Shuffle

variable {p q : ℕ}

def IsMixedBoundary (s : Shuffle p q) (i : Fin (p + q + 1)) : Prop :=
  ∃ lower upper : Fin (p + q),
    lower.val + 1 = upper.val ∧ i = upper.castSucc ∧
      Xor (lower ∈ s.leftPositions) (upper ∈ s.leftPositions)

noncomputable def mixedBoundaryFaces (p q : ℕ) :
    Finset (Shuffle p q × Fin (p + q + 1)) := by
  classical
  exact Finset.univ.filter fun si => IsMixedBoundary si.1 si.2

noncomputable def nonmixedBoundaryFaces (p q : ℕ) :
    Finset (Shuffle p q × Fin (p + q + 1)) := by
  classical
  exact Finset.univ.filter fun si => ¬ IsMixedBoundary si.1 si.2

private abbrev MixedBoundaryFace (p q : ℕ) :=
  {si : Shuffle p q × Fin (p + q + 1) // IsMixedBoundary si.1 si.2}

private noncomputable instance : Fintype (MixedBoundaryFace p q) :=
  Fintype.ofFinite _

private def mixedBoundaryFaceOfMixedFace (x : MixedFace p q) :
    MixedBoundaryFace p q :=
  ⟨(x.shuffle, x.faceIndex),
    ⟨x.lowerPosition, x.upperPosition, x.adjacent, rfl, x.mixed⟩⟩

private noncomputable def mixedFaceOfMixedBoundaryFace (z : MixedBoundaryFace p q) :
    MixedFace p q :=
  let lower := z.2.choose
  let upper := z.2.choose_spec.choose
  { shuffle := z.1.1
    lowerPosition := lower
    upperPosition := upper
    adjacent := z.2.choose_spec.choose_spec.1
    mixed := z.2.choose_spec.choose_spec.2.2 }

private theorem mixedFaceOfMixedBoundaryFace_faceIndex (z : MixedBoundaryFace p q) :
    (mixedFaceOfMixedBoundaryFace z).faceIndex = z.1.2 := by
  change z.2.choose_spec.choose.castSucc = z.1.2
  exact z.2.choose_spec.choose_spec.2.1.symm

private noncomputable def mixedFaceEquivMixedBoundaryFace :
    MixedFace p q ≃ MixedBoundaryFace p q where
  toFun := mixedBoundaryFaceOfMixedFace
  invFun := mixedFaceOfMixedBoundaryFace
  left_inv x := by
    apply MixedFace.ext
    · rfl
    · apply Fin.ext
      have hupper :
          (mixedFaceOfMixedBoundaryFace
              (mixedBoundaryFaceOfMixedFace x)).upperPosition =
            x.upperPosition := by
        have hface := mixedFaceOfMixedBoundaryFace_faceIndex
          (mixedBoundaryFaceOfMixedFace x)
        change
          (mixedFaceOfMixedBoundaryFace
              (mixedBoundaryFaceOfMixedFace x)).upperPosition.castSucc =
            x.upperPosition.castSucc at hface
        exact Fin.castSucc_inj.mp hface
      have hadjacent :=
        (mixedFaceOfMixedBoundaryFace
          (mixedBoundaryFaceOfMixedFace x)).adjacent
      have hadjacentX := x.adjacent
      have hupperVal := congrArg Fin.val hupper
      change
        (mixedFaceOfMixedBoundaryFace
          (mixedBoundaryFaceOfMixedFace x)).lowerPosition.val =
            x.lowerPosition.val
      omega
    · apply Fin.ext
      have hupper :
          (mixedFaceOfMixedBoundaryFace
              (mixedBoundaryFaceOfMixedFace x)).upperPosition =
            x.upperPosition := by
        have hface := mixedFaceOfMixedBoundaryFace_faceIndex
          (mixedBoundaryFaceOfMixedFace x)
        change
          (mixedFaceOfMixedBoundaryFace
              (mixedBoundaryFaceOfMixedFace x)).upperPosition.castSucc =
            x.upperPosition.castSucc at hface
        exact Fin.castSucc_inj.mp hface
      exact congrArg Fin.val hupper
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact mixedFaceOfMixedBoundaryFace_faceIndex z

private theorem sum_mixedBoundaryFace_eq_zero {A : Type*} [AddCommGroup A]
    (f : Shuffle p q → Fin (p + q + 1) → A)
    (hf : ∀ x : MixedFace p q,
      f x.partner.shuffle x.partner.faceIndex = f x.shuffle x.faceIndex) :
    ∑ z : MixedBoundaryFace p q,
      shuffleSignZ z.1.1 • f z.1.1 z.1.2 = 0 := by
  rw [← Fintype.sum_equiv mixedFaceEquivMixedBoundaryFace
    (fun x : MixedFace p q => shuffleSignZ x.shuffle • f x.shuffle x.faceIndex)
    (fun z : MixedBoundaryFace p q => shuffleSignZ z.1.1 • f z.1.1 z.1.2)
    (fun _ => rfl)]
  apply MixedFace.sum_shuffleSignZ_smul_eq_zero
  intro x
  exact hf x

theorem sum_mixedBoundaryFaces_eq_zero {A : Type*} [AddCommGroup A]
    (f : Shuffle p q → Fin (p + q + 1) → A)
    (hf : ∀ x : MixedFace p q,
      f x.partner.shuffle x.partner.faceIndex = f x.shuffle x.faceIndex) :
    ∑ z ∈ mixedBoundaryFaces p q,
      shuffleSignZ z.1 • f z.1 z.2 = 0 := by
  classical
  rw [mixedBoundaryFaces, ← Finset.sum_subtype_eq_sum_filter]
  simpa using sum_mixedBoundaryFace_eq_zero f hf

theorem sum_boundary_eq_sum_nonmixedBoundaryFaces
    {A : Type*} [AddCommGroup A]
    (f : Shuffle p q → Fin (p + q + 1) → A)
    (hf : ∀ x : MixedFace p q,
      f x.partner.shuffle x.partner.faceIndex = f x.shuffle x.faceIndex) :
    ∑ z : Shuffle p q × Fin (p + q + 1),
        shuffleSignZ z.1 • f z.1 z.2 =
      ∑ z ∈ nonmixedBoundaryFaces p q,
        shuffleSignZ z.1 • f z.1 z.2 := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Shuffle p q × Fin (p + q + 1)))
    (fun z => IsMixedBoundary z.1 z.2)
    (fun z : Shuffle p q × Fin (p + q + 1) =>
      shuffleSignZ z.1 • f z.1 z.2)
  have hmixed :
      ∑ z ∈ (Finset.univ : Finset (Shuffle p q × Fin (p + q + 1))) with
          IsMixedBoundary z.1 z.2,
        shuffleSignZ z.1 • f z.1 z.2 = 0 := by
    simpa [mixedBoundaryFaces] using sum_mixedBoundaryFaces_eq_zero f hf
  rw [hmixed, zero_add] at h
  simpa [nonmixedBoundaryFaces] using h.symm

end Shuffle

end AlgebraicTopology.EilenbergZilber
