---
article_id: af_766c432515315b9337d99707
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.polyBernoulli_negative_symmetric_exponential_generating_function
---

# Poly Bernoulli Symmetric Exponential Generating Function

The symmetric bivariate exponential generating function for negative-index poly-Bernoulli
numbers, identified by their closed formula in terms of Stirling numbers of the second kind.

Math notes: `hB` is Kaneko's closed formula; `hxy` is the domain
`(e^|x| - 1)(e^|y| - 1) < 1` of absolute convergence of the double series (all `B n k ≥ 0`).
The weaker condition `|(e^x - 1)(e^y - 1)| < 1` does not suffice: at `x = -3`,
`y = log 1.9` the outer series diverges.

Proof: The Stirling EGF is derived from the finite-difference formula, then absolute convergence
permits a Fubini rearrangement and a geometric-series sum, following Hamahata–Masubuchi,
Theorems 2 and 4, and Kaneko's original formula.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Has Sum stirling Second succ egf](../../../../Combinatorics/MathlibExt/part-01/enumerative/part-08/stirling-second-explicit/has-sum-stirling-second-succ-egf.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.PolyBernoulliSymmetricExponentialGeneratingFunction](../../../../../sources/v2/MathlibExt.md)
- Y. Hamahata and H. Masubuchi, "Special Multi-Poly-Bernoulli Numbers," Journal of Integer Sequences 10 (2007), Article 07.4.1, Theorem 4 (symmetric formula), lines 180–186, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex>; the closed formula identifying `B` is Theorem 2 there, lines 156–166. Both are attributed there to M. Kaneko, "Poly-Bernoulli numbers," Journal de Théorie des Nombres de Bordeaux 9 (1997), 221–228.
