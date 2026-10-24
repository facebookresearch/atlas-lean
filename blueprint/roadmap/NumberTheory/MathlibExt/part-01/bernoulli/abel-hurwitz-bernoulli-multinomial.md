---
article_id: af_e94ef5f1d219a3b64f72dfbc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.abel_hurwitz_bernoulli_multinomial
---

# Abel Hurwitz Bernoulli

Abel-Hurwitz-Bernoulli multinomial identity: for `2 ≤ m`,
`x : Fin m → ℚ` and `r : Fin m`, summing over `l : Fin m → ℕ`
with `∑ l = n`, the multinomial-weighted sum of `B_{l_r}(x_r + l_r)`
times `∏_{j≠r} (x_j + l_j)^{l_j}` equals the single sum
`∑_{l=0}^n C(n,l) ((m+l-2)!/(m-2)!) B_{n-l}(∑ x_i + n)`.

The source states the identity for arbitrary real or complex parameters. This
target intentionally records its rational specialization, using
`Polynomial.eval`; the corresponding complex formulation would instead use
`Polynomial.eval₂ (algebraMap ℚ ℂ)`.

`B_k = Polynomial.bernoulli k` evaluated with `Polynomial.eval`;
`C(n; l) = Nat.multinomial Finset.univ l`. Distinct from the same
paper's equation (5.11) single-sum Abel-Bernoulli identity and from
the Carlitz Bernoulli-number symmetry.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.AbelHurwitzBernoulli](../../../../../sources/v2/MathlibExt.md)
- Claudio de J. Pita Ruiz V., "Carlitz-Type and Other Bernoulli Identities," Journal of Integer Sequences 19 (2016), Article 16.1.8, Proposition [Abel-Hurwitz-Bernoulli identity] (a), equation (5.16), lines 821–829, https://cs.uwaterloo.ca/journals/JIS/VOL19/Pita/pita23.tex
