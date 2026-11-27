# Gross-substitutes success-probability function

A set function $f : 2^A \to \mathbb{R}$ is gross substitutes if for all price vectors $p \le q$ in $\mathbb{R}_{\ge 0}^A$ and every set $S \in \arg\max_T \bigl(f(T) - p(T)\bigr)$ there is a set $S' \in \arg\max_T \bigl(f(T) - q(T)\bigr)$ with $\{ a \in S : p_a = q_a \} \subseteq S'$. In a combinatorial contract instance, the success function is gross substitutes if $f$ has this property; every gross-substitutes function is submodular, and additive, unit-demand and matroid-rank functions are gross substitutes.

## Depends on

- [Combinatorial-actions contract with a binary outcome](combinatorial-actions-binary-outcome-contract.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021; SIAM Journal on Computing 54(6) (2025), arXiv:2109.14260.
