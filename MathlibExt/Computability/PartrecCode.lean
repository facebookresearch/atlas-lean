/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Computable families of codes
-/
module

public import Mathlib.Computability.PartrecCode

/-!
# Computable families of codes

A parametrized form of the s-m-n theorem (`Nat.Partrec.Code.smn`): a partial recursive function
`F : α → ℕ →. ℕ` of a `Primcodable` parameter is computed by a computable family of codes
`g : α → Code`, with `(g a).eval = F a`. The family is `a ↦ curry U (encode a)` for one code `U`
of the uncurried function.

## Main results

- `exists_computable_code`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open Encodable
open Nat.Partrec (Code)

/-- **Parametrized s-m-n theorem.** Let $\alpha$ be a type with a primitive recursive encoding into
the natural numbers, and for each $a \in \alpha$ let $F_a$ be a partial function from
$\mathbb{N}$ to $\mathbb{N}$, such that $(a, x) \mapsto F_a(x)$ is partial recursive. Then there
is a computable map $g$ from $\alpha$ to codes of partial recursive functions such that for all
$a \in \alpha$ and $x \in \mathbb{N}$, the partial function with code $g(a)$ agrees with $F_a$ at
$x$: both are undefined, or both are defined with the same value. -/
theorem exists_computable_code {α : Type*} [Primcodable α] {F : α → ℕ →. ℕ} (hF : Partrec₂ F) :
    ∃ g : α → Code, Computable g ∧ ∀ a x, (g a).eval x = F a x := by
  have hG : Partrec fun m : ℕ ↦ (Part.ofOption (decode (α := α) m.unpair.1)).bind
      fun a ↦ F a m.unpair.2 :=
    Partrec.bind (Computable.ofOption (Computable.decode.comp
      (Computable.fst.comp Computable.unpair)))
      (hF.comp Computable.snd (Computable.snd.comp (Computable.unpair.comp Computable.fst)))
  obtain ⟨U, hU⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hG)
  refine ⟨fun a ↦ Code.curry U (encode a),
    (Code.primrec₂_curry.comp (Primrec.const U) Primrec.encode).to_comp, fun a x ↦ ?_⟩
  rw [Code.eval_curry, hU]
  simp only [Nat.unpair_pair, encodek, Part.coe_some, Part.bind_some]

end MetaMathlibExt
