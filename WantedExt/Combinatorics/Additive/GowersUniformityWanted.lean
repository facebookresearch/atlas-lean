/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Additive.GowersNorm
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Gowers uniformity norms: wanted theorems

Results built on the Gowers norms of `MathlibExt.Combinatorics.Additive.GowersNorm`: the `U³`
inverse theorem of Green and Tao over `𝔽₅ⁿ` and Gowers's quantitative bound for Szemerédi's
theorem.

Sources (numbering as indicated):

* [G01] W. T. Gowers, *A new proof of Szemerédi's theorem*, Geom. Funct. Anal. 11 (2001)
  465–588; numbering of the author's preprint `sz898.dvi`,
  https://www.dpmms.cam.ac.uk/~wtg10/papers.html (journal numbering not checked).
* [GT08] B. Green and T. Tao, *An inverse theorem for the Gowers `U³(G)` norm*, Proc. Edinb.
  Math. Soc. 51 (2008) 73–153; numbering of arXiv:math/0503014.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Finset MathlibExt.Combinatorics.Additive.GowersNorm

namespace MathlibExt.Combinatorics.Additive.GowersUniformityWanted

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
/-- **Inverse theorem for the `U³` norm over `𝔽₅ⁿ`.** Let `f : 𝔽₅ⁿ → ℂ` be bounded by `1` and
let `0 < η ≤ 1` with `‖f‖_{U³} ≥ η`. Then there are a subspace `W` of codimension at most
`(2/η)^C`, a point `y` and a function `φ : 𝔽₅ⁿ → ℝ/ℤ` that is a quadratic phase locally on
`y + W` (its third differences `(h₁·∇)(h₂·∇)(h₃·∇)φ(x)` vanish whenever the cube
`(x + ω · h)_{ω ∈ {0,1}³}` lies in `y + W`, that is, whenever `x ∈ y + W` and
`h₁, h₂, h₃ ∈ W`) such that `|𝔼_{x ∈ y + W} f(x) e(-φ(x))| ≥ (η/2)^C`, with `C = 2^16`.
This is the "in particular" form of Theorem 2.3(i) of Green and Tao [GT08]: there the
conclusion is `‖f‖_{u³(y + W)} ≥ (η/2)^C`, a supremum over the local quadratic phases of their
Definition 2.1; the supremum is attained because it is that of a continuous function on a
compact set, so the two forms are equivalent. -/
theorem_wanted u3_inverse_F5 (n : ℕ) (f : (Fin n → ZMod 5) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hU : η ≤ gowersNorm 3 f) :
    ∃ (W : Submodule (ZMod 5) (Fin n → ZMod 5)) (y : Fin n → ZMod 5)
      (φ : (Fin n → ZMod 5) → UnitAddCircle),
      (Module.finrank (ZMod 5) ((Fin n → ZMod 5) ⧸ W) : ℝ) ≤ (2 / η) ^ (2 ^ 16 : ℕ) ∧
      (∀ x h₁ h₂ h₃, x - y ∈ W → h₁ ∈ W → h₂ ∈ W → h₃ ∈ W →
        φ (x + h₁ + h₂ + h₃) - φ (x + h₁ + h₂) - φ (x + h₁ + h₃) - φ (x + h₂ + h₃) +
          φ (x + h₁) + φ (x + h₂) + φ (x + h₃) - φ x = 0) ∧
      (η / 2) ^ (2 ^ 16 : ℕ) ≤
        ‖𝔼 x ∈ univ.filter (fun x => x - y ∈ W),
          f x * conj ((AddCircle.toCircle (φ x) : Circle) : ℂ)‖

/-- **Gowers's bound for Szemerédi's theorem.** Let `0 < δ ≤ 1/2`, let `k` be a positive integer
and let `N ≥ 2^(2^((1/δ)^(2^(2^(k+9)))))`. Then every subset of `{1, …, N}` of size at least
`δN` contains an arithmetic progression of length `k`: Theorem 18.6 of Gowers [G01], whose
bound `2 ↑ 2 ↑ δ⁻¹ ↑ 2 ↑ 2 ↑ (k + 9)` is right-associated. Progressions have nonzero common
difference here; Gowers's Corollary 3.6 counts exactly such "genuine" progressions. The
qualitative statement is `MathlibExt.Combinatorics.Additive.SzemerediWanted.szemeredi`. -/
theorem_wanted szemeredi_gowers_bound (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (k : ℕ)
    (hk : 0 < k) (N : ℕ)
    (hN : (2 : ℝ) ^ ((2 : ℝ) ^ (δ⁻¹ ^ (2 ^ (2 ^ (k + 9)) : ℕ))) ≤ N)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (hdens : δ * N ≤ A.card) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

end MathlibExt.Combinatorics.Additive.GowersUniformityWanted
