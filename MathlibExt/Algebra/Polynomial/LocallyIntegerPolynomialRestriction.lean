/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomial
import Mathlib.Data.Set.Finite.Basic

/-!
# Restriction of locally integer polynomial functions

Agreement on an infinite subset forces the difference of two locally integer polynomial
functions to vanish identically.

## References

* Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025), Article A41,
  pp. 1–16, Corollary 1 and Lemma 3.
* Sayak Sengupta, *Nilpotent polynomials over $\mathbb{Z}$*, arXiv:2401.01435 (2024).
  Borisov cites this preprint in Section 1 as motivation for studying these rings.
-/

namespace MetaMathlibExt

/-- **Locally integer polynomial functions agreeing on an infinite subset are equal.** Let
$U \subseteq V \subseteq \mathbb{Z}$ with $U$ infinite, and let $f, g : V \to \mathbb{Z}$ lie in
the ring $\mathrm{LIP}(V)$ of locally integer polynomial functions on $V$. If $f(x) = g(x)$ for
every $x \in U$, then $f = g$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 1 (`integers-2025-A41-cor-1`). -/
public theorem lip_restrict_injective {U V : Set ℤ} (hU : U.Infinite) (hUV : U ⊆ V)
    {f g : V → ℤ} (hf : f ∈ lipSubring V) (hg : g ∈ lipSubring V)
    (h : f ∘ Set.inclusion hUV = g ∘ Set.inclusion hUV) : f = g := by
  let : Infinite U := hU.to_subtype
  have himage : (Set.inclusion hUV '' (Set.univ : Set U)).Infinite :=
    Set.infinite_univ.image (Set.inclusion_injective hUV).injOn
  have hzeros : {x : V | (f - g) x = 0}.Infinite := himage.mono <| by
    rintro _ ⟨x, -, rfl⟩
    exact sub_eq_zero.mpr (congrFun h x)
  have hzero := lip_eq_zero_of_infinite_zeros ((lipSubring V).sub_mem hf hg) hzeros
  funext x
  exact sub_eq_zero.mp (congrFun hzero x)

end MetaMathlibExt
