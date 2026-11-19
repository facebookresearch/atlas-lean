# Gowers norms dominate the mean

Let $G$ be a finite abelian group and let $\mathbb{E}$ denote an average over $G$. For every $d \ge 1$ and $f : G \to \mathbb{C}$, $|\mathbb{E} f| \le \|f\|_{U^d}$, by [monotonicity](gowers-norm-le-gowers-norm-succ.md) from $\|f\|_{U^1} = |\mathbb{E} f|$.

For the indicator of a set $A$ of density $\delta$ this says $\|1_A\|_{U^d} \ge \delta$: by the [cube formula](gowers-pow-eq-cube-average.md), $A$ contains at least $\delta^{2^d} |G|^{d+1}$ cubes of dimension $d$. That is Lemma 3.7 of Gowers, which he proves by induction on $d$ and averaging rather than by monotonicity. A random set of density $\delta$ has about that many cubes, and sets that are uniform of degree $d - 1$ nearly attain the bound (his Lemma 3.10).

## Background

- [Sidorenko's inequality for the four-cycle, graphon form](../../../../GraphTheory/extremal-graph-theory/sidorenko-s-conjecture/graphon-hom-density-cycle-graph-four-ge.md): the case $d = 2$ is the four-cycle case of Sidorenko's inequality for the sum graph of $A$, the symmetric kernel $W(x, y) = 1_A(x + y)$ on $G \times G$ (a step graphon), whose four-cycle density is $\|1_A\|_{U^2}^4$ and whose edge density is $\delta$.

## Sources

- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, Lemmas 3.7 and 3.10.
- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, (1.2).
