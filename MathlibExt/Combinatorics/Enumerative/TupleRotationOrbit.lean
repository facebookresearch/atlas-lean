/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Rotation orbits of tuples

The cyclic group `C_n` acts on `n`-tuples `x : Fin n → α` by rotation, here through the powers of
`finRotate n`, and the orbits of this action are the `n`-necklaces. This is Definition 2.3 of the
arXiv text of Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*
(arXiv:2405.08937v4), published in the Journal of Integer Sequences 29 (2026), Article 26.4.6,
where the generator of `C_n` rotates the other way; both generate the same group of rotations,
so the orbits agree.

## Main definitions

* `MetaMathlibExt.tupleRotationOrbit x`: the set of the tuples `x ∘ finRotate n ^ m`, `m : ℕ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Rotation orbit of a tuple.** Let $x = (x_0, \dots, x_{n-1})$ be a tuple of length $n$ with
entries in a type $\alpha$, and let $\sigma$ be the cyclic rotation of $\{0, \dots, n-1\}$ that
sends $i$ to $i + 1$ for $i < n - 1$ and sends $n - 1$ to $0$. The rotation orbit of $x$ is the
set of tuples $x \circ \sigma^m$ for $m \in \mathbb{N}$, that is, of the cyclic shifts
$(x_m, x_{m+1}, \dots, x_{m+n-1})$ of $x$, with indices taken modulo $n$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Definition 2.3 (the action of `C_n` by
rotation; necklaces are its orbits), used by Theorem 16 (`jis-2026-26.4.6-thm-16`). -/
def tupleRotationOrbit {α : Type*} {n : ℕ} (x : Fin n → α) : Set (Fin n → α) :=
  {y | ∃ m : ℕ, y = x ∘ ⇑((finRotate n) ^ m)}

/-- **A tuple lies in its own rotation orbit.** Every tuple $x$ of length $n$ with entries in a
type $\alpha$ belongs to the rotation orbit of $x$.

Source: Grinberg and Mao, Journal of Integer Sequences 29 (2026), Article 26.4.6,
Definition 2.3. -/
theorem self_mem_tupleRotationOrbit {α : Type*} {n : ℕ} (x : Fin n → α) :
    x ∈ tupleRotationOrbit x :=
  ⟨0, by simp⟩

/-- **One-step rotation stays in the rotation orbit.** For every tuple
$x = (x_0, \dots, x_{n-1})$ with entries in a type $\alpha$, the tuple whose $i$-th entry is
$x_{i+1}$, indices taken modulo $n$ (that is, $(x_1, \dots, x_{n-1}, x_0)$ when $n \ge 1$), lies in
the rotation orbit of $x$.

Source: Grinberg and Mao, Journal of Integer Sequences 29 (2026), Article 26.4.6,
Definition 2.3. -/
theorem comp_finRotate_mem_tupleRotationOrbit {α : Type*} {n : ℕ} (x : Fin n → α) :
    x ∘ ⇑(finRotate n) ∈ tupleRotationOrbit x :=
  ⟨1, by simp⟩

end

end MetaMathlibExt
