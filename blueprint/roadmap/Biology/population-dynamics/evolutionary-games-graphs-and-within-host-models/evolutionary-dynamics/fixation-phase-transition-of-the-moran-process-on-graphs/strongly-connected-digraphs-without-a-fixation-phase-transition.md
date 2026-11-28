# Strongly connected digraphs without a fixation phase transition

Consider the Moran process on a strongly connected directed graph $G$: a vertex reproduces with probability proportional to its fitness and places its offspring on a uniformly random out-neighbour. Let $f_{G,r}$ be the fixation probability of a single mutant of fitness $r$ placed at a uniformly random vertex.

**Theorem.** There is a class $\mathcal{G}$ of strongly connected digraphs and a function $C : \mathbb{R}_{>0} \to \mathbb{R}_{>0}$ such that for every $r > 0$ and every sufficiently large $G \in \mathcal{G}$,

$$
\frac{1}{C(r)\,|V(G)|} \le f_{G,r} \le \frac{C(r)}{|V(G)|}.
$$

Quantitatively, for the digraphs $G_{k,a}$ of the construction with $a = \lceil 4r \rceil$, $r > 1$: for all $k \ge 2$ an advantageous mutant fixates with probability at most $72 r \log_2(r+1)/|V(G_{k,a})|$, and for $k \ge 7 + \lceil \log_2(5r^2) \rceil$ a disadvantageous mutant of fitness $1/r$ fixates with probability at least $1/\big(|V(G_{k,a})|\,(9r)^{60r^2}\big)$.

## Expansion

The construction is a hierarchy of levels in which a mutant must repeatedly "spawn" into the next level before it is overwritten from a single source vertex; the escape probability decays geometrically with the level, which caps fixation at order $1/n$ even for $r > 1$, while the same geometry keeps a disadvantageous mutant alive with probability of order $1/n$. This contrasts with [undirected graphs](fixation-phase-transition-on-undirected-graphs.md), where every large graph separates $r < 1$ from $r > 1$ by more than any polylogarithmic factor: directed suppressors of selection can erase the phase transition entirely.

## Sources

- Leslie Ann Goldberg, John Lapinskas and David Richerby, *Phase Transitions of the Moran Process and Algorithmic Consequences*, arXiv:1804.02293, Theorem 3 (Section 1) and Theorems 60 and 61 (Section 7). <https://doi.org/10.48550/arXiv.1804.02293> Published version: Random Structures & Algorithms 56 (2019) 597–647, <https://doi.org/10.1002/rsa.20890>.
