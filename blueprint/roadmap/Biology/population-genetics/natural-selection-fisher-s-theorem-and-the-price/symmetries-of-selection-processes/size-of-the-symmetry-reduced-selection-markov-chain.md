# Size of the symmetry-reduced selection Markov chain

**Setting.** Let $(G, p)$ be a selection process on $n = |G|$ sites with symmetry group $\mathrm{Sym}(G,p)$ of order $S$, acting on states by $\mathbf x \mapsto \mathbf x_\sigma$. Its orbits $[\mathbf x] = \{\mathbf x_\sigma : \sigma \in \mathrm{Sym}(G,p)\}$ are the states of the *reduced chain* $\mathcal R(G,p)$, with transition probabilities

$$P_{[\mathbf x] \to [\mathbf y]} = \sum_{\mathbf z \in [\mathbf y]} P_{\mathbf x \to \mathbf z},$$

which do not depend on the representative $\mathbf x$ because symmetries preserve transition probabilities. Equivalent states carry the same number of $1$ alleles.

**Theorem.** The number $R$ of states of $\mathcal R(G,p)$ satisfies

$$\max\Big(n + 1,\ 2 + \frac{2^n - 2}{S}\Big) \ \le\ R\ \le\ 2 + \frac{1}{S}\sum_{k=1}^{n-1}\binom{n}{k}\gcd\big(S,\ k!\,(n-k)!\big).$$

For a well-mixed haploid population ($S = n!$) the lower bound $n+1$ is attained: the reduced chain is the usual chain on the number of mutants. The bounds quantify how much a structured population (small $S$) resists reduction from the $2^n$ raw states.

## Depends on

- [Symmetries of a selection process preserve transition probabilities](symmetries-of-a-selection-process-preserve-transition-probabilities.md)

## Proof depends on

- [Lagrange's theorem: the order of a group is the number of cosets of a subgroup times its order](../../../../GroupTheory/group-basics/lagrange-theorem.md)

## Expansion

The monochromatic states $\mathbf 0$ and $\mathbf 1$ are fixed by every symmetry and give two orbits. The remaining states split by the number $k \in \{1, \dots, n-1\}$ of $1$ alleles, each class containing at least one orbit, which gives $R \ge n+1$; and each orbit has at most $S$ elements, which gives $R - 2 \ge (2^n - 2)/S$. For the upper bound, the states with $k$ ones form a set of size $\binom nk$ on which the group acts; an orbit has size $S/|\mathrm{Stab}|$, and a stabiliser of a $k$-subset embeds in $\mathrm{Sym}(k) \times \mathrm{Sym}(n-k)$, so by Lagrange its order divides $\gcd(S, k!(n-k)!)$. Hence each orbit has at least $S/\gcd(S, k!(n-k)!)$ elements, and the number of orbits at level $k$ is at most $\binom nk \gcd(S, k!(n-k)!)/S$.

## Sources

- Benjamin Allen, "Symmetry in models of natural selection", *Journal of The Royal Society Interface* 20 (2023), 20230306, <https://doi.org/10.1098/rsif.2023.0306>. Numbering as in the preprint arXiv:2307.06495v1, <https://arxiv.org/abs/2307.06495v1>: Section 5 and Theorem 2 (proved in Appendix A).
