---
article_id: af_b4f62ab1ce47b6fb93f84671
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.fibonomial_prime_cube_congr
---

# Kimball Webb Fibonomial Congruence

Kimball–Webb Fibonomial congruence modulo `p³` (Fibonacci case).

Fibonacci specialization only: the Fibonomial `{(k+1)ρ-1 choose ρ-1}_F` is
`ε^k` mod `p³` where `ρ = p - ε` is the rank of appearance of `p`; this is
not Ballot's general Lucasnomial theorem `thm:N`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Padics.KimballWebbFibonomialCongruence](../../../../../sources/v2/MathlibExt.md)
- Christian Ballot, *The Congruence of Wolstenholme for Generalized Binomial Coefficients Related to Lucas Sequences*, Journal of Integer Sequences 18 (2015), Article 15.5.4, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Ballot/ballot14.tex>, Theorem `thm:KW` (rewriting Lemma 3 of Kimball and Webb), equation `eq:Fib`, lines 144-150.
