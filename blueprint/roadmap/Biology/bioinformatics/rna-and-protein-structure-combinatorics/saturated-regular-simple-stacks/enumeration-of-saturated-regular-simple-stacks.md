# Enumeration of saturated regular simple stacks

**Definitions.** A diagram on $[n]$ is a set of arcs $(i,j)$, $i<j$. A *stack* is a noncrossing diagram (no $i<k<j<l$ with arcs $(i,j),(k,l)$). It is *$m$-regular* if every arc has length $j-i\ge m$, and *simple* if every vertex has degree at most $1$; an RNA secondary structure is a 2-regular simple stack. An *extended* $m$-regular simple stack allows the two terminal vertices $1$ and $n$ degree up to $2$. A structure is *saturated* if no arc can be added without violating the length, degree or noncrossing constraints (local minima of the Nussinov–Jacobson energy, which counts $-1$ per arc). A structure is *$k$-saturated* if it is saturated and has exactly $k$ fewer arcs than an optimal (maximum-arc) structure.

**Theorem (saturated $m$-regular simple stacks).** The number $R_s(n,k;m)$ of saturated $m$-regular simple stacks on $[n]$ with $k$ arcs is

$$R_s(n,k;m)=[x^{n-2k}y^k]\,\frac{\bigl(y-y^2+xy+x^{m-1}(1-y)^2-x^{m+1}\bigr)^{k+1}}{(k+1)(1-x)^{k+1}(1-y)^{2(k+1)}}\qquad(n,k\ge0).$$

For $m=2$,

$$R_s(n,k;2)=\frac{1}{k+1}\sum_{t=1}^{k+1}\binom{k+1}{t}\binom{2t+k-1}{t-1}\binom{t}{n-2k-t}.$$

Since the number of $k$-saturated 2-regular simple stacks is $LO_k(n)=R_s(n,\lfloor\frac{n-1}2\rfloor-k;2)$, this recovers Clote's count of optimal structures ($LO_0(n)=1$ for odd $n$, $n(n+2)/8$ for even $n$) and gives closed forms such as $LO_1(n)=\frac{(n-1)(n-3)}{192}(n^2+8n+31)$ for odd $n\ge3$ and $LO_1(n)=\frac{(n-2)(n-4)}{9216}(n^4+12n^3+68n^2-288n-2304)$ for even $n$.

**Theorem (extended stacks).** The number $ELO(n,k)$ of saturated extended 2-regular simple stacks with $n\ge6$ vertices and $k\ge3$ arcs is

$$ELO(n,k)=\sum_{t=1}^{k+1}\sum_{i=1}^{4}\binom{k+1}{t}\binom{2t+k}{t-1}\binom{t}{n-2k-2-t+i}P_i(k,t),$$

with explicit rational functions $P_i(k,t)$ (falling-factorial denominators), e.g.

$$P_1(k,t)=\frac{2(k-t+1)}{(k+1)_3(k+2t)_2}\bigl(k^3+(4t-2)k^2+(2t^2-4t+1)k-2t^3-4t^2+4t\bigr).$$

It is obtained by summing a uniform formula over the six types of primary component (the connected components containing vertices $1$ and $n$), and it specializes to the known count of optimal extended 2-regular simple stacks.

## Expansion

The Schmitt–Waterman bijection maps secondary structures to linear trees, and a Schröder-tree-type bijection maps unlabelled linear trees to forests of small trees, each with labelled ($(n-k+1)!$ to one) and asterisked leaves. Saturation translates into two local restrictions on the trees: the fiber of each outermost internal vertex has $m-1$ or $m$ leaves, and every other fiber has at most $m$ consecutive leaves. The forests satisfying these restrictions factor as $(k+1)$-th powers of a bivariate series, and Lagrange-type extraction gives the coefficient formula. Extended stacks are handled by first fixing the primary component and its four kinds of attached substructures, then counting the remaining forests.

## Sources

- Q. Guo, Y. Jin, L. H. Sun, M. Weng, "A semi-bijective algorithm for saturated extended 2-regular simple stacks", arXiv:2112.13087 (2021), Section 1 (definitions, Clote's and Guo et al.'s formulas), Theorem 1, Theorem 2, Corollaries 1–2, Theorem 3, <https://doi.org/10.48550/arXiv.2112.13087>.
