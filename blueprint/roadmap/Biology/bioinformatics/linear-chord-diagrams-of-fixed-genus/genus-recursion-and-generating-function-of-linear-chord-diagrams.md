# Genus recursion and generating function of linear chord diagrams

**Setting.** A **linear chord diagram** with $n$ chords is a perfect matching of $2n$ points on a horizontal backbone, drawn as arcs in the upper half-plane. Collapsing the backbone to a single vertex makes it a fatgraph with one vertex and $n$ edges; if it has $r$ boundary components, its **genus** $g$ satisfies $r=n+1-2g$. Let $\mathbf c_g(n)$ count linear chord diagrams of genus $g$ with $n$ chords and $\mathbf C_g(z)=\sum_{n\ge0}\mathbf c_g(n)z^n$; genus-$0$ diagrams are noncrossing and $\mathbf c_0(n)$ is the Catalan number. In RNA terms, chords are base pairs and genus $g\ge1$ measures the topological complexity of pseudoknots.

**Harer–Zagier identity.** With $P(n,x)=\sum_{g}\mathbf c_g(n)\,x^{n+1-2g}$,

$$
1+2\sum_{n\ge0}\frac{P(n,x)}{(2n-1)!!}\,z^{n+1}=\left(\frac{1+z}{1-z}\right)^{x}.
$$

**Recursion.** For $g\ge1$, with $\mathbf c_g(n)=0$ for $2g>n$,

$$
(n+1)\,\mathbf c_g(n)=2(2n-1)\,\mathbf c_g(n-1)+(2n-1)(n-1)(2n-3)\,\mathbf c_{g-1}(n-2).
$$

**Theorem.** For every $g\ge1$,

$$
\mathbf C_g(z)=P_g(z)\,\frac{\sqrt{1-4z}}{(1-4z)^{3g}}=z^{2g}R_g(z)\,(1-4z)^{\frac12-3g},
$$

where $P_g$ has integer coefficients, degree at most $3g-1$, $P_g(1/4)\ne0$ and lowest term $z^{2g}$; equivalently $R_g$ is an integer polynomial of degree at most $g-1$ with $R_g(1/4)\ne0$ and $R_g(0)=\mathbf c_g(2g)\ne0$. Hence $\mathbf C_g$ is algebraic over $\mathbb C(z)$, as for the Catalan generating function, with unique singularity $z=1/4$ independent of $g$, and

$$
\mathbf c_g(n)\sim\frac{P_g(1/4)}{\Gamma(3g-1/2)}\,n^{3g-\frac32}\,4^n.
$$

**Closed forms.**

$$
\mathbf c_1(n)=\frac{2^{n-2}(2n-1)!!}{3\,(n-2)!}\ (n\ge2),\qquad \mathbf c_2(n)=\frac{2^{n-4}(5n-2)(2n-1)!!}{90\,(n-4)!}\ (n\ge4),
$$

$$
\mathbf c_3(n)=\frac{2^{n-6}(35n^2-77n+12)(2n-1)!!}{5670\,(n-6)!}\ (n\ge6),\qquad \mathbf c_g(2g)=\frac{(4g)!}{4^g\,(2g+1)!},
$$

and $\sum_{g\ge0}\mathbf c_g(2g)\frac{x^{2g}}{(2g)!}=\frac{\sqrt{1+2x}-\sqrt{1-2x}}{2x}$.

## Expansion

A linear chord diagram with $n$ chords is a pair of permutations, the backbone cycle and the fixed-point-free involution of chords, and the boundary components of the fatgraph are the cycles of their product. The Harer–Zagier formula, from the matrix-model computation of the Euler characteristic of moduli space, counts these by number of boundary cycles. Differentiating it in $z$ and comparing coefficients gives a three-term recursion; translated to generating functions it becomes a first-order linear ODE for $\mathbf C_g$ with inhomogeneity built from $\mathbf C_{g-1}$, whose solution by induction on $g$ has the stated algebraic form. Taking $n=2g$ in the recursion, where $\mathbf c_g(2g-1)=0$, gives the closed form for diagrams with the minimum number of chords.

## Sources

- J. E. Andersen, R. C. Penner, C. M. Reidys and M. S. Waterman, "Enumeration of linear chord diagrams", arXiv (2010), Section 2 "Background and Notation" (fatgraphs and linear chord diagrams) and Section 3 "The generating function of linear chord diagrams of genus $g$" (Harer–Zagier lemma, recursion lemma, main theorem and the two corollaries with explicit $\mathbf c_1,\mathbf c_2,\mathbf c_3$ and $\mathbf c_g(2g)$), <https://doi.org/10.48550/arXiv.1010.5614>
