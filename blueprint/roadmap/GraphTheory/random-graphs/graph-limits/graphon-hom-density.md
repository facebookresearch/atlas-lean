# Homomorphism density in a graphon

For a simple graph $F$ on $\{1, \dots, k\}$ and a graphon $W$,

$$t(F, W) = \int_{[0,1]^k} \prod_{ij \in E(F)} W(x_i, x_j) \, dx_1 \cdots dx_k ,$$

each edge counted once. If $W_G$ is the step function of a graph $G$ with at least one vertex (constant $\beta_{ij}$ on the square of side $1/|V(G)|$ indexed by $i, j$), then $t(F, W_G) = t(F, G)$.

## Background

- [Graphon](../finitely-forcible-graphons/is-graphon.md): graphons as functions of two real variables of which only the values on $[0,1]^2$ matter.
- [Homomorphism density](hom-density.md): the finite version.

## Sources

- L. Lovász and B. Szegedy, "Limits of dense graph sequences", *J. Combin. Theory Ser. B* 96 (2006), 933–957, arXiv:math/0408173, §2.5.
- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, §3.1, equations (3.1)–(3.2).
