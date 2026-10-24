---
article_id: af_32e08798837c5244ca57c466
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.filipponi_binomial_sum_formula_general
---

# Filipponi binomial sum formula general

Filipponi binomial-sum formula for the incomplete Fibonacci triangle.

Hacène Belbachir and Amine Belkhir, "Combinatorial Expressions Involving Fibonacci,
Hyperfibonacci, and Incomplete Fibonacci Numbers", Journal of Integer Sequences 17 (2014),
Article 14.4.3. The formula is attributed there to P. Filipponi, "Incomplete Fibonacci and
Lucas numbers", Rend. Circ. Mat. Palermo 45 (1996), 37–56, DOI 10.1007/BF02845088.

Authoritative source: <https://cs.uwaterloo.ca/journals/JIS/VOL17/Belbachir/belb2.tex>.
Live/source file SHA-256
`e60c0875f28ac5be72af638a5a6d955c789993dfeed0f463afbb34955be8f2fe`.

Source definition of `f_r(s) = ∑_{j=0}^s choose(r-j,j)` at lines 304–319, and formula
`f_(n+2h)(k+h) = ∑_{j=0}^h choose(h,j) f_(n+j)(k+j)` at lines 347–371; extracted statement text
SHA-256 `c34b4ffa5811994595d796e20d6310141e9e6214ad20c93468c26bf2bc1233db`.

Stable task identifier `jis_grounded_1b088a32a9d82c1527d97e03__filipponi_binomial_sum_formula`.

All indices and inclusive bounds are preserved exactly: the defining sum runs `j = 0..s`
via `Finset.range (s + 1)`, and the outer sum runs `j = 0..h` via
`Finset.range (h + 1)`.

The truncated-subtraction identity holds unconditionally: out-of-range binomial
terms vanish, so no range hypotheses are needed.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.FilipponiBinomialSum](../../../../../../../sources/v2/MathlibExt.md)
