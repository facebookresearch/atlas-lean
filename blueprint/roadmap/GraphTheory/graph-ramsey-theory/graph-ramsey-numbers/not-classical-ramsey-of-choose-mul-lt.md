# Erdős's bound: the Ramsey property fails

If $\binom nk 2^{1 - \binom k2} < 1$, then the Ramsey property for $(k, k)$ fails on $n$ vertices: some graph on $n$ vertices contains no $K_k$, and neither does its complement. This restates the [existence form](exists-not-is-contained-of-choose-mul-lt.md) in terms of [the Ramsey property for cliques](classical-ramsey.md). For example $\binom 64 2^{-5} = 15/32 < 1$ gives $R(4,4) > 6$, and $\binom{11}5 2^{-9} = 462/512 < 1$ gives $R(5,5) > 11$.

## Informally uses

- [Erdős's lower bound for diagonal Ramsey numbers (existence form)](exists-not-is-contained-of-choose-mul-lt.md): the graph witnessing the failure.

## Sources

- Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Theorem 1.4.
