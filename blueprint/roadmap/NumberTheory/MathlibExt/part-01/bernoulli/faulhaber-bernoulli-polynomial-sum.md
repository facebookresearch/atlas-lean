---
article_id: af_db1f6d967d30fa224aa0924c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.faulhaber_bernoulli_polynomial_sum
---

# Faulhaber Bernoulli Polynomial Summation

Faulhaber-type Bernoulli polynomial summation formula as a polynomial
identity in `ℚ[X]` for the sum of shifted Bernoulli polynomials.

The sum `Σ_{j=1}^n B_k(X + j)` is expanded in the `B_{k-r}(X)` basis with
coefficients from `B_{r+1}` evaluated at `n + 1` and Bernoulli numbers.
Proves `Wanted` entry `faulhaber_bernoulli_polynomial_sum`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.FaulhaberBernoulliPolynomialSummation](../../../../../sources/v2/MathlibExt.md)
- Claudio de J. Pita Ruiz V., *Carlitz-Type and Other Bernoulli Identities*, Journal of Integer Sequences 19 (2016), Article 16.1.8, <https://cs.uwaterloo.ca/journals/JIS/VOL19/Pita/pita23.tex>, Proposition [Faulhaber-type formula], equation (5.32), lines 1001-1007.
