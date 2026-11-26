/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Frobenius in normal-basis coordinates

## References

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
  Journal of Integer Sequences 29 (2026), Article 26.4.6, pp. 1–31, §9.2, Lemma 28
  (equivariance for the generator).
- Christophe Reutenauer, *Free Lie Algebras*, London Mathematical Society Monographs,
  New Series 7, Clarendon Press, 1993, §7.6.2 (the coordinate map used by Grinberg and Mao).
-/

namespace MetaMathlibExt

-- The extension field's finiteness is a hypothesis of the result, not data in its conclusion.
set_option linter.unusedFintypeInType false in
/-- **Normal basis coordinates turn Frobenius into rotation.** Let $K$ be a finite field that is an
algebra over a finite field $F$, let $q = |F|$ and $n = [K : F]$, and let $\beta \in K$ be such
that $\beta, \beta^q, \dots, \beta^{q^{n-1}}$ are linearly independent over $F$. Define
$\Phi : F^n \to K$ by $\Phi(a_0, \dots, a_{n-1}) = \sum_{i=0}^{n-1} a_i \beta^{q^i}$. Then $\Phi$ is
a bijection, and for every $a \in F^n$,
$$\Phi(a_0, \dots, a_{n-1})^q = \Phi(a_{n-1}, a_0, a_1, \dots, a_{n-2}),$$
that is, raising to the $q$-th power rotates the coordinates one step.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 28, with `Φ` as defined in
Section 9 of the arXiv text (`jis-2026-26.4.6-lem-28`). -/
public theorem normalBasisMap_bijective_frobenius (F K : Type*)
    [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K] (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ)))) :
    Function.Bijective (fun a : Fin n → F => ∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) ∧
      ∀ a : Fin n → F, (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) ^ Fintype.card F =
        ∑ i, (a ∘ ⇑(finRotate n).symm) i • β ^ (Fintype.card F ^ (i : ℕ)) := by
  classical
  let q := Fintype.card F
  let b := basisOfLinearIndependentOfCardEqFinrank'
    (fun i : Fin n ↦ β ^ (q ^ (i : ℕ))) hβ (by simpa using hn.symm)
  have hb : ⇑b = fun i : Fin n ↦ β ^ (q ^ (i : ℕ)) :=
    coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  constructor
  · have hfun : (fun a : Fin n → F => ∑ i, a i • β ^ (q ^ (i : ℕ))) = ⇑b.equivFun.symm := by
      funext a
      rw [Module.Basis.equivFun_symm_apply, hb]
    change Function.Bijective (fun a : Fin n → F => ∑ i, a i • β ^ (q ^ (i : ℕ)))
    rw [hfun]
    exact b.equivFun.symm.bijective
  intro a
  have hcard : Fintype.card K = q ^ n := by simpa [q] using Module.card_fintype b
  have hwrap : β ^ (q ^ n) = β := hcard ▸ FiniteField.pow_card β
  have hrotate (i : Fin n) : (β ^ (q ^ (i : ℕ))) ^ q = β ^ (q ^ (finRotate n i : ℕ)) := by
    rw [← pow_mul, ← pow_succ]
    cases n with
    | zero => exact Fin.elim0 i
    | succ m =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [finRotate_last] using hwrap
      · rw [show finRotate (m + 1) j.castSucc = j.succ from finRotate_of_lt j.isLt]
        rfl
  change (FiniteField.frobeniusAlgHom F K) (∑ i, a i • β ^ (q ^ (i : ℕ))) = _
  rw [map_sum]
  refine Fintype.sum_equiv (finRotate n) _ _ fun i ↦ ?_
  rw [map_smul]
  change a i • (β ^ (q ^ (i : ℕ))) ^ q =
    a ((finRotate n).symm (finRotate n i)) • β ^ (q ^ (finRotate n i : ℕ))
  rw [Equiv.symm_apply_apply, hrotate]

end MetaMathlibExt
