/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace IntermediateField

/-- **Kummer correspondence.** Let `F` contain a primitive `n`-th root of unity, with `0 < n`,
and let `P` be the subgroup of `n`-th powers in `Fˣ`. The finite abelian Galois intermediate
extensions `E` of `F` in `AlgebraicClosure F` with Galois group of exponent dividing `n`
correspond bijectively to the subgroups `B` of `Fˣ` containing `P` with finite relative index
`[B : P]`. The forward map takes the preimage `B(E)` of the `n`-th powers of `Eˣ` under
`Fˣ → Eˣ`; the inverse adjoins all `n`-th roots of elements of `B` in the fixed closure.
All `n`-th roots of unity lie in `F`, so adjoining one root for each element gives the same field.

For a corresponding pair, `[E : F] = [B(E) : P]`. The quotient `B(E) / P` is isomorphic
as a group to the group of homomorphisms from `Gal(E/F)` to the `n`-th roots of unity in `F`.
The character of a class represented by `a` evaluates at `σ` as `σ(α) / α` in `E` for any
`n`-th root `α` of `a` in `E`. In particular, the trivial extension corresponds to `P`.

Sources: J. S. Milne, *Fields and Galois Theory*, v5.10, §5, Theorem 5.30 and the preceding
isomorphism (pp. 75–76); *Class Field Theory*, v4.03, Chapter VII, Appendix A, Theorem A.3. -/
public theorem_wanted kummerCorrespondence {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    let P : Subgroup Fˣ := (powMonoidHom n).range
    let radicands (E : IntermediateField F (AlgebraicClosure F)) : Subgroup Fˣ :=
      (powMonoidHom n : Eˣ →* Eˣ).range.comap (Units.map (algebraMap F E))
    let extensions := {E : IntermediateField F (AlgebraicClosure F) //
      FiniteDimensional F E ∧ IsGalois F E ∧ IsMulCommutative (E ≃ₐ[F] E) ∧
        Monoid.exponent (E ≃ₐ[F] E) ∣ n}
    let subgroups := {B : Subgroup Fˣ // P ≤ B ∧ Finite (B ⧸ P.subgroupOf B)}
    ∃ e : extensions ≃ subgroups,
      (∀ E, (e E).1 = radicands E.1) ∧
      (∀ B, (e.symm B).1 = IntermediateField.adjoin F
        {x : AlgebraicClosure F | ∃ b : B.1, x ^ n = algebraMap F _ ((b.1 : Fˣ) : F)}) ∧
      ∀ E : extensions,
        let B := radicands E.1
        Module.finrank F E.1 = P.relIndex B ∧
          ∃ χ : (B ⧸ P.subgroupOf B) ≃* ((E.1 ≃ₐ[F] E.1) →* rootsOfUnity n F),
            ∀ (a : B) (α : E.1ˣ), α ^ n = Units.map (algebraMap F E.1) a.1 →
              ∀ σ : E.1 ≃ₐ[F] E.1,
                algebraMap F E.1 ((χ (QuotientGroup.mk a) σ).1 : F) =
                  σ (α : E.1) / (α : E.1)

end IntermediateField
