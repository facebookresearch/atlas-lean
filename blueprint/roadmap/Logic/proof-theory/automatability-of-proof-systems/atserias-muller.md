# Atserias–Müller: automating resolution is NP-hard

Write $r(G)$ for the size of a CNF formula $G$ and $s(G)$ for the length of its shortest resolution refutation ($s(G) = \infty$ if $G$ is satisfiable). There are constants $c, d > 0$ such that it is NP-hard, given a CNF formula $G$, to distinguish $s(G) < r(G)^{c}$ from $s(G) > 2^{r(G)^{1/d}}$; the second case includes satisfiable formulas, and no promise of unsatisfiability is made. In particular it is NP-hard to approximate $s$ within a factor $2^{r^{1/2 - \varepsilon}}$ for every $\varepsilon > 0$.

Say that resolution is automatable in time $t$ if some algorithm, given an unsatisfiable CNF formula $F$, outputs a resolution refutation of $F$ in time $t(r(F) + s(F))$. If $t$ is time-constructible, non-decreasing and subexponential ($t(n) \le 2^{n^{o(1)}}$) and resolution is automatable in time $t$, then there are polynomials $q, p$ such that $3$-SAT on $n$ variables is decidable in time $O(t(p(n)) + q(n))$. Consequently resolution is not automatable in polynomial time unless $\mathrm{P} = \mathrm{NP}$, not in quasi-polynomial time unless $\mathrm{NP} \subseteq \mathrm{QP}$, and not in subexponential time unless $\mathrm{NP} \subseteq \mathrm{SUBEXP}$.

## Proof sketch

Given a $3$-CNF formula $F$, compute $G(F)$ by the reduction, of size $r \le n^{O(1)}$, and run the automating algorithm on $G(F)$ for $t(r + r^{c})$ steps, checking whether its output is a valid resolution refutation of $G(F)$. If $F$ is satisfiable, $G(F)$ is unsatisfiable with $s(G(F)) < r^{c}$, so a refutation appears in time and the answer is "satisfiable". If $F$ is unsatisfiable, $G(F)$ has no refutation of length at most $2^{r^{1/d}}$, which exceeds the time bound because $t$ is subexponential, so no valid refutation is output (in particular none when $G(F)$ is satisfiable), and the answer is "unsatisfiable".

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Proof depends on

- [The Atserias–Müller reduction from SAT to resolution proof size](am-reduction-formula.md)

## Sources

- A. Atserias, M. Müller, "Automating resolution is NP-hard", FOCS (2019); Journal of the ACM 67 (2020), arXiv:1904.02991 (Theorems 1, 2 and 13).
