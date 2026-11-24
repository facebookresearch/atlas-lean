# Counting lemma

Let $F$ be a simple graph and let $w, w'$ be weighted graphs on the same finite vertex set with all edge weights in $[0, 1]$. Then

$$|t(F, w) - t(F, w')| \le |E(F)| \cdot \|w - w'\|_\square .$$

So homomorphism densities are Lipschitz in the cut distance: graphs that are close in the cut norm have close subgraph densities. The proof changes one edge weight at a time; each step is the integral of $(w - w')(x_i, x_j)$ against factors in $[0,1]$ that depend on $x_i$ alone or on $x_j$ alone, which the cut norm bounds after integrating out the two endpoints.

## Background

- [Counting lemma for graphons](abs-graphon-hom-density-sub-le.md): the same inequality for graphons.
- [Lovász–Szegedy limit theorem](exists-graphon-limit.md): the limit theorem's proof applies this inequality to a graph and its weakly regular partition average.

## Sources

- L. Lovász and B. Szegedy, "Limits of dense graph sequences", *J. Combin. Theory Ser. B* 96 (2006), 933–957, arXiv:math/0408173, Lemma 4.1 and inequality (7).
- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, Theorem 2.7 (a) (constant $4$, for edge weights in $[-1, 1]$).
