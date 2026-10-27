---
article_id: af_e7ba1a2e37fc457a6618e2e8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ridout_padic_roth
---

# Ridout Padic Roth

Ridout's p-adic extension of Roth's theorem: for an irrational algebraic real `ξ`,
`ε > 0`, and a finite set of primes `S`, only finitely many rationals
satisfy `(∏ ℓ ∈ S, |p|_ℓ * |q|_ℓ) * |ξ - p / q| < 1 / H ^ (2 + ε)`,
where `H = max |p| q` is the canonical rational height.
The source prints the right side as `1 / q ^ (2 + ε)` for reduced fractions
`p / q` with `q > 0`; since this file quantifies over all `r : ℚ` (including
integers and large numerators with small denominators), the denominator alone
does not control the height (e.g. `r = 2 ^ k` has `r.den = 1`), so the
statement uses `H = max r.num.natAbs r.den` in place of the printed `q`.
Denominator-only bounds are false over all of `ℚ`: with `2 ∈ S`,
`r = 2 ^ k` gives LHS `= 1 - √2 / 2 ^ k < 1 =` RHS for every `k ≥ 1`,
so the standard projective height is required for finiteness.
p-adic normalization: `|ℓ|_ℓ = ℓ⁻¹`, formalized by `padicNorm`.
Rational solutions `p / q` are canonical reduced rationals via `r.num`
and `r.den`.

Proof: The proof follows Roth's auxiliary-polynomial and index route, with the
S-adic integrality step supplied by valuation divisibility and a finite pigeonhole.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Roth Auxiliary](finite-of-divisible-approximations.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.RidoutPadicRoth](../../../../sources/v2/MathlibExt.md)
- Boris Adamczewski, "The Many Faces of the Kempner Number", Journal of Integer Sequences 16 (2013), Article 13.2.15, `thmRi` environment, lines 736–746, attributed there to Ridout, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Adamczewski/adam6.tex>.
