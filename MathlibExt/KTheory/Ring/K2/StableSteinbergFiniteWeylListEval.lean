/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylWord

/-! # List-level evaluation of finite Weyl words

For ranks `n m : ℕ`, endpoint functions `a b : Fin m → ℕ` with pointwise bounds
`ha : ∀ k, a k < n` and `hb : ∀ k, b k < n`, pointwise distinctness
`hab : ∀ k, a k ≠ b k`, and units `u : Fin m → Rˣ` over `[CommRing R]`,
`finiteWeyl_list_toStableE_eq` lifts `finiteWeyl_toStableE_eq_finiteElementary`
through the head-left `List.ofFn`/`List.prod` word: the `toStableE` image of the
ordered product of the stable `weyl (a k) (b k) (hab k) (u k)` generators equals
the ordered product of their three-factor finite `StableE.elementary`
realizations, with the same `Fin n` transports, signs, inverses, and factor
orientation as the single-generator theorem. Both sides use `List.ofFn` index
order, so the empty list (`m = 0`) gives `1 = 1`. Purpose: list-level finite
word realization input for the central-monomial containment route. Nonclaims: no
monomial product uniqueness, torus landing,
`finiteCentralKernelSubgroup ≤ finiteTorusSubgroup`, TWT, kernel-generation, or
Matsumoto claim.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {R : Type u} [CommRing R]

/-- List-level `StableE` image of a finite Weyl word: `toStableE` of the
head-left `List.ofFn`/`List.prod` ordered product of
`weyl (a k) (b k) (hab k) (u k)` over `k : Fin m` is the ordered product of the
three-factor finite `StableE.elementary` realizations at `⟨a k, ha k⟩`,
`⟨b k, hb k⟩` with coefficients `u k`, `-(u k)⁻¹`, `u k`, in the same head-left
order and orientation as `finiteWeyl_toStableE_eq_finiteElementary`. Hypotheses
are the pointwise bounds `ha hb` and distinctness `hab`; the empty list gives
`1 = 1`. Purpose: finite word realization input. Nonclaims: no monomial product
uniqueness, torus landing, central-kernel containment, TWT, kernel-generation,
or Matsumoto claim. -/
public theorem finiteWeyl_list_toStableE_eq
    (n m : ℕ) (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (u : Fin m → Rˣ) :
    StableSteinberg.toStableE (R := R)
        ((List.ofFn (fun k => StableSteinberg.weyl (a k) (b k) (hab k) (u k))).prod) =
      (List.ofFn (fun k =>
        StableE.elementary n ⟨a k, ha k⟩ ⟨b k, hb k⟩
          (fun h => hab k (congrArg Fin.val h)) (↑(u k) : R) *
        StableE.elementary n ⟨b k, hb k⟩ ⟨a k, ha k⟩
          (fun h => (hab k).symm (congrArg Fin.val h)) (-(↑(u k)⁻¹ : R)) *
        StableE.elementary n ⟨a k, ha k⟩ ⟨b k, hb k⟩
          (fun h => hab k (congrArg Fin.val h)) (↑(u k) : R))).prod := by
  let word := Matrix.GeneralLinearGroup.FiniteWeylWord.ofBoundedNat
    a b ha hb hab u
  have hword := StableSteinberg.toStableE_evalFiniteWeylWord word
  simpa only [word,
    StableSteinberg.evalFiniteWeylWord_ofBoundedNat,
    StableSteinberg.evalFiniteWeylWordInStableE_ofBoundedNat] using hword

end AlgebraicKTheory

end
