# Compactness of the graphon space

Every sequence of graphons $W_n$ (values in $[0, 1]$) has a subsequence $W_{n_k}$ and a graphon $W$ with $\delta_\square(W_{n_k}, W) \to 0$. Equivalently, after identifying graphons at cut distance $0$, the space of graphons with the cut distance is a compact metric space; since simple graphs are dense in it, it is the completion of the space of graphs in the cut distance.

## Background

- [Cut distance of graphons](cut-distance.md): the metric.
- [Lovász–Szegedy limit theorem](exists-graphon-limit.md): together with the equivalence of left and cut-distance convergence, compactness gives another proof that convergent graph sequences have limits.

## Sources

- L. Lovász and B. Szegedy, "Szemerédi's lemma for the analyst", *Geom. Funct. Anal.* 17 (2007) (preprint 2006, reference [29] of Borgs et al.), as quoted in C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, Proposition 3.6 (with $I = [0, 1]$).
