/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Third rack homology of dihedral quandles (Fenn–Rourke–Sanderson, Ohtsuki Conjecture 5.12)

T. Ohtsuki (ed.), Problems on invariants of knots and 3-manifolds, Conjecture 5.12 (R. Fenn, C.
Rourke, B. Sanderson): `H₃(R_p) ≅ ℤ ⊕ ℤ/pℤ` for `p` prime.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Quandle
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Defs

@[expose] public section

namespace MathlibExt.Topology.DihedralQuandleRackHomologyAMR103Problem0108Wanted

/-!
Source: T. Ohtsuki (ed.), Problems on invariants of knots and 3-manifolds, Geom. Topol. Monogr. 4
(2002), Conjecture 5.12 (R. Fenn, C. Rourke, B. Sanderson). UnsolvedMath record UM-10400108
(`AMR-103-0108`), dataset ulamai/UnsolvedMath v1.8.0.

`H₃` is rack homology and `R_p` the dihedral quandle on `ℤ/p`, `a * b = 2b - a` in
Niebrzydowski–Przytycki's notation, which is Mathlib's `Quandle.Dihedral p` with action
`Quandle.dihedralAct p b a = 2b - a` (`b ◃ a`). The chain group `C_m = ℤ[R_pᵐ]` is free abelian on
`m`-tuples, with Niebrzydowski–Przytycki's Definition 1.1(i) boundary `∂(x₁, …, x_m) = ∑_{i=2}^{m}
(-1)^i ((…, x̂ᵢ, …) - (x₁ * xᵢ, …, x_{i-1} * xᵢ, x_{i+1}, …))`; `H₃ = ker ∂₃ / im ∂₄`. Only odd
primes are covered: for `p = 2`, `R_2` is the trivial two-element quandle, all boundaries vanish and
`H₃ = ℤ⁸`, so the source's "`p` prime" is false at `p = 2`; Niebrzydowski–Przytycki state and prove
the conjecture for odd primes.
-/

/-- The rack chain group `C_m(R_p) = ℤ[R_pᵐ]`, free abelian on `m`-tuples of elements of `ZMod p`
(the underlying set of `Quandle.Dihedral p`). -/
abbrev RackChain (p m : ℕ) : Type :=
  (Fin m → ZMod p) →₀ ℤ

/-- Delete the `j`-th entry of `x`. -/
def rackFaceDelete {p m : ℕ} (x : Fin (m + 1) → ZMod p) (j : Fin (m + 1)) : Fin m → ZMod p :=
  x ∘ j.succAbove

/-- Act by the `j`-th entry on the entries before it, then delete the `j`-th entry:
`(x₁ * xⱼ, …, xⱼ₋₁ * xⱼ, xⱼ₊₁, …)`, where `a * b = 2b - a` is Mathlib's dihedral quandle action
`Quandle.dihedralAct p b a` (the quandle `Quandle.Dihedral p` on `ZMod p`, written `b ◃ a`). -/
def rackFaceAct {p m : ℕ} (x : Fin (m + 1) → ZMod p) (j : Fin (m + 1)) : Fin m → ZMod p :=
  fun k => if j.succAbove k < j then Quandle.dihedralAct p (x j) (x (j.succAbove k))
    else x (j.succAbove k)

/-- The rack boundary `∂ : C_{m+1} → C_m`, `∂(x) = ∑_{i=2}^{m+1} (-1)^i (dᵢ⁰ x - dᵢ¹ x)` with `dᵢ⁰`
deleting and `dᵢ¹` acting (Fenn–Rourke–Sanderson; Niebrzydowski–Przytycki, Definition 1.1(i)); the
position `i` is `j + 1` for `j : Fin (m + 1)`. -/
noncomputable def rackBoundary (p m : ℕ) : RackChain p (m + 1) →ₗ[ℤ] RackChain p m :=
  Finsupp.linearCombination ℤ fun x => ∑ j : Fin (m + 1),
    if (j : ℕ) = 0 then 0 else
      (-1 : ℤ) ^ ((j : ℕ) + 1) •
        (Finsupp.single (rackFaceDelete x j) 1 - Finsupp.single (rackFaceAct x j) 1)

/-- The third rack homology group `H₃ᴿ(R_p) = ker ∂₃ / im ∂₄`. -/
abbrev rackH3 (p : ℕ) : Type :=
  LinearMap.ker (rackBoundary p 2) ⧸
    (LinearMap.range (rackBoundary p 3)).comap (LinearMap.ker (rackBoundary p 2)).subtype

/-- The Fenn–Rourke–Sanderson conjecture (Ohtsuki, Problems on invariants of knots and
3-manifolds, Conjecture 5.12) for odd primes: `H₃ᴿ(R_p) ≅ ℤ ⊕ ℤ/p`. -/
def fennRourkeSandersonConjecture : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → Nonempty (rackH3 p ≃+ ℤ × ZMod p)

/--
Resolved true: Niebrzydowski and Przytycki proved that the third rack homology of the dihedral
quandle `R_p` is `ℤ ⊕ ℤ/p` for every odd prime `p`. Source: T. Ohtsuki (ed.), Problems on invariants
of knots and 3-manifolds, Geom. Topol. Monogr. 4 (2002), Conjecture 5.12 (R. Fenn, C. Rourke, B.
Sanderson); resolution: M. Niebrzydowski and J. H. Przytycki, Homology of dihedral quandles, J. Pure
Appl. Algebra 213 (2009), 742-755, arXiv:math/0611803, Section 3, "The proof of the
Fenn-Rourke-Sanderson conjecture": H₃ᴿ(R_p) = ℤ ⊕ ℤ_p for p an odd prime (Conjecture 1.4 there,
quoting Ohtsuki 5.12), via H₃ᴿ = H₃^Q ⊕ ℤ and H₃^Q(R_p) = ℤ_p (Mochizuki's cocycle and universal
coefficients), https://arxiv.org/abs/math/0611803.
-/
public theorem_wanted fennRourkeSandersonConjecture_holds : fennRourkeSandersonConjecture

end MathlibExt.Topology.DihedralQuandleRackHomologyAMR103Problem0108Wanted
