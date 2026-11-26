# XOS set functions, demand queries and value queries

A set function $f : 2^A \to \mathbb{R}_{\ge 0}$ is XOS (fractionally subadditive) if there is a finite family of nonnegative additive functions $a^1, \dots, a^K$ (all $a^k_x \ge 0$) with $f(S) = \max_k \sum_{x \in S} a^k_x$ for all $S$. Every monotone submodular function with $f(\emptyset) = 0$ is XOS, and every XOS function is monotone and subadditive. A value query returns $f(S)$ for a given $S$; a demand query, given prices $p \in \mathbb{R}_{\ge 0}^A$, returns a set in $\arg\max_S \bigl(f(S) - \sum_{x \in S} p_x\bigr)$. Algorithms for combinatorial contracts measure complexity in the number of such queries.

## Depends on

- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- B. Lehmann, D. Lehmann, N. Nisan, "Combinatorial auctions with decreasing marginal utilities", Games and Economic Behavior 55(2) (2006).
- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Multi-Agent Contracts", STOC 2023, arXiv:2211.05434.
