# Gross-substitutes success-probability function

A monotone set function $f : 2^A \to \mathbb{R}$ with $f(\emptyset) = 0$ is gross substitutes if for all price vectors $p \le q$ in $\mathbb{R}_{\ge 0}^A$ and every set $S \in \arg\max_T \bigl(f(T) - p(T)\bigr)$ there is a set $S' \in \arg\max_T \bigl(f(T) - q(T)\bigr)$ with $\{ a \in S : p_a = q_a \} \subseteq S'$; this is the gross-substitutes condition for valuations, with the actions as items. In a combinatorial contract instance, whose success function $f : 2^A \to [0, 1]$ is monotone with $f(\emptyset) = 0$, the success function is gross substitutes if $f$ has this property. Such an $f$ is submodular, since gross-substitutes valuations are, and additive and unit-demand success functions are gross substitutes. Monotonicity matters: $f(\emptyset) = 0$ and $f(S) = -1$ for $S \ne \emptyset$ satisfies the price condition, because $\emptyset$ is the only demanded set at nonnegative prices, but is not submodular.

## Depends on

- [Combinatorial-actions contract with a binary outcome](combinatorial-actions-binary-outcome-contract.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [Gross-substitutes valuation](../../combinatorial-auctions/gross-substitutes-valuation.md)
- [Gross-substitutes valuations are submodular](../../combinatorial-auctions/gross-substitutes-valuations-are-submodular.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021; SIAM Journal on Computing 54(6) (2025), arXiv:2109.14260.
