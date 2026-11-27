/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.FourierTransformFiniteGroup

@[expose] public section

open scoped BigOperators
open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup

namespace MathlibExtTest.RepresentationTheory.FourierTransformFiniteGroup

/-- At the trivial representation the Fourier transform is the total mass. -/
example {G : Type} [Group G] [Fintype G] (P : G → ℂ) :
    fourier (Representation.trivial ℂ G ℂ) P = (∑ s, P s) • 1 := by
  simp only [fourier, Finset.sum_smul]
  rfl

/-- Convolving with the point mass at the identity changes nothing. -/
example {G : Type} [Group G] [Fintype G] [DecidableEq G] (P : G → ℂ) :
    convPow P 1 = P := by
  funext s
  simp [convPow, conv]

/-- The transform of a two-step walk is the square of the one-step transform. -/
example {G V : Type} [Group G] [Fintype G] [DecidableEq G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (Q : G → ℂ) :
    fourier ρ (convPow Q 2) = fourier ρ Q * fourier ρ Q := by
  rw [fourier_convPow, sq]

/-- Schur's lemma consequence, used on a class function: the character of an irreducible
representation, seen as a function on the group, has scalar transform. -/
example {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ∃ c : ℂ, fourier ρ ρ.character = c • 1 :=
  ⟨_, fourier_eq_smul_one_of_isClassFunction ρ ρ.character fun g h => ρ.char_conj g h⟩

/-- On complex values `conv` is the repository's convolution on a finite group. -/
example {G : Type} [Group G] [Fintype G] (P Q : G → ℂ) (s : G) :
    conv P Q s = MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv P Q s := by
  rw [conv_eq_finiteGroupConv]

end MathlibExtTest.RepresentationTheory.FourierTransformFiniteGroup
