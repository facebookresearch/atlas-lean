# Random pairs of codes are two-sided robustly testable

For every rate pair $0 < \rho_1, \rho_2 < 1$ there exist $\kappa, \delta > 0$ such that for all sufficiently large $\Delta$, a uniformly random pair of linear codes $C_1, C_2 \subseteq \mathbb{F}_2^{\Delta}$ with $\dim C_i = \lceil \rho_i \Delta \rceil$ satisfies with probability $1 - o(1)$: both $C_i$ and $C_i^{\perp}$ have relative distance at least $\delta$, and both $C_1 \otimes C_2$ and its dual tensor code are $\kappa$-agreement testable.

## Proof sketch

Agreement testability of $C_1 \otimes C_2$ fails only if some low-weight pattern of row and column disagreements is not explained by a tensor codeword. One shows a combinatorial characterization in terms of distance of the codes restricted to large subsets of coordinates and then a union bound over subsets and a first-moment computation over random generator matrices; the dual statement is symmetric because the duals of random codes are random codes.

## Depends on

- [Agreement testability and robustness of tensor codes](agreement-testability-tensor.md)

## Proof depends on

- [Agreement testability and robustness of tensor codes](agreement-testability-tensor.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- P. Panteleev, G. Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022), arXiv:2111.03654.
- G. Kalachev, P. Panteleev, "Two-sided robustly testable codes", arXiv:2206.09973 (2022).
