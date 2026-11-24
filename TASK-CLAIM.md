# Task claim: binomial expansion of the partial sums of Chebyshev polynomials

This temporary note opens the draft pull request that claims the ATLAS task
`af_2e233586971585ad4e923102`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Algebra/orthogonal-polynomials/kassel-reutenauer-polynomials/chebyshev-cpartial-sum-eq-binomial-sum.md`
- Lean declaration: `MetaMathlibExt.chebyshevCPartialSum_eq_binomial_sum`, a `theorem_wanted` in
  `WantedExt/Algebra/IntertwinedIntegerSequencesWanted.lean`
- Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of
  Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.4.

Statement to prove, with its name and statement unchanged: let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every $n \ge 1$,

$$F_n = \sum_{m=0}^{\lfloor n/2 \rfloor} (-1)^m \binom{n-m}{m} X^{n-2m} +
\sum_{m=0}^{\lfloor (n-1)/2 \rfloor} (-1)^m \binom{n-m-1}{m} X^{n-2m-1}.$$
