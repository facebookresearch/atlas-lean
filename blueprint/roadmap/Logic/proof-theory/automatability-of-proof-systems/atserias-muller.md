# Atserias–Müller: automating resolution is NP-hard

It is NP-hard to find, given an unsatisfiable CNF formula $F$, a resolution refutation of $F$ of size polynomial in the size of the shortest resolution refutation. More precisely, it is NP-hard to distinguish CNF formulas that have resolution refutations of polynomial size from those that have no resolution refutation of size $2^{n^{\varepsilon}}$. Consequently resolution is not automatable unless $\mathrm{P} = \mathrm{NP}$, not automatable in quasi-polynomial time unless $\mathrm{NP} \subseteq \mathrm{QP}$, and not automatable in subexponential time unless $\mathrm{NP} \subseteq \mathrm{SUBEXP}$.

## Proof sketch

Run a hypothetical automating algorithm on $\mathrm{Ref}(F)$ for a polynomial time bound: by the reduction, it terminates with a refutation exactly when $F$ is satisfiable, up to the gap between polynomial and $2^{n^{\varepsilon}}$ sizes, so it decides $3$-SAT.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Proof depends on

- [The Atserias–Müller reduction from SAT to resolution proof size](am-reduction-formula.md)

## Sources

- A. Atserias, M. Müller, "Automating resolution is NP-hard", FOCS (2019); Journal of the ACM 67 (2020), arXiv:1904.02991.
