---
article_id: af_45ac34ce17243bbc6c6c3e2f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalizedCatalanSchroeder_generatingFunction
---

# Generalized Catalan Schroeder generating Function

Ordinary generating function of the generalized Catalan-Schroeder recurrence
with `a 0 = 1`, `a 1 = p` and
`a n = s * a (n - 1) + t * ∑_{k=0}^{n-3} a (k+1) * a (n-k-2)` for `n ≥ 2`,
stated as `mk a = g * subst f C` with `g = (1 + (p-s+t) * X) / (1 - (s-2*t) * X)`,
`f = t * X * (1 + (p-s+t) * X) / (1 - (s-2*t) * X) ^ 2`, and `C` the Catalan
generating series built from Mathlib's `catalan` numbers.
The cited TeX prints `f` without the second `X` in the factor `(1 + (p-s+t) * X)`.
That version is false (for `s = 2`, `t = 1`, `p = 2` its coefficient of `X` is `3`,
not `a 1 = 2`); the recurrence forces the factor restored here.

Proof: Map Mathlib's Catalan power-series equation to `R`, substitute `f`, derive the same
quadratic equation as the recurrence by unit cancellation, and conclude by coefficientwise
uniqueness. This is a direct power-series derivation of Barry's cited proposition.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Generalized Catalan Schroeder recurrence functional Equation](generalized-catalan-schroeder-recurrence.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GeneralizedCatalanSchroeder](../../../../../../../sources/v2/MathlibExt.md)
- Paul Barry, "Generalized Catalan Recurrences, Riordan Arrays, Elliptic Curves, and Orthogonal Polynomials", Journal of Integer Sequences 24 (2021), Article 21.5.1, Proposition lines 367-373, <https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry/barry431.tex>.
