# Equidistant cone of circular split networks

**Setting.** Leaves $1, \dots, n$ and a root $0$ are placed in circular order $0, 1, \dots, n$. A *split* is a bipartition $A|B$ of $\{0, \dots, n\}$; it is *circular* if both parts are intervals of the circular order. A *rooted circular split system* $N$ with nonnegative weights $\mathbf{a} = (a_{A|B})$ defines the distance $\delta_{N,\mathbf{a}}(i,j) = \sum_{A|B \in N \text{ separating } i, j} a_{A|B}$, and the network is *equidistant* if $\delta_{N,\mathbf a}(0, i)$ is the same for all leaves $i$. The *complete circular split system* $KN_n$ consists of all $\binom{n+1}{2} - 1$ circular splits (all diagonals of the $(n+1)$-gon plus the $n$ leaf splits). The *equidistant cone* of $N$ is

$$EDC_N = \{\delta_{N,\mathbf a} : \mathbf a \ge 0,\ (N, \delta_{N,\mathbf a}) \text{ equidistant}\} \subseteq \mathbb{R}^{\binom n2},$$

recorded on leaf pairs.

**Background (Kalmanson).** A metric $\delta$ on a finite set is the distance of some weighted circular split system if and only if, for some circular ordering, every $i < j < k < l$ satisfies $\delta(i,j) + \delta(k,l) \le \delta(i,k) + \delta(j,l)$ and $\delta(i,l) + \delta(j,k) \le \delta(i,k) + \delta(j,l)$.

**Theorem.**
1. *(Facets.)* With $[i,j] = \{i, \dots, j\}$, the facets of $EDC_{KN_n}$ are given by

$$\delta(1,i) \le \delta(1,i+1),\qquad \delta(i,n) \le \delta(i-1,n) \qquad (i \in [2, n-1]),$$

$$\delta(i-1, i+1) \le \delta(i-1,i) + \delta(i, i+1) \qquad (i \in [2, n-1]),$$

$$\delta(i,j) + \delta(i-1, j+1) \le \delta(i, j+1) + \delta(i-1, j) \qquad (i < j \in [2, n-1]),$$

the left, right, triangle and covering inequalities.
2. *(Faces.)* For every rooted circular split system $N$ on these leaves, $EDC_N$ is a face of $EDC_{KN_n}$, and every face of $EDC_{KN_n}$ is of this form.
3. *(Ehrhart theory.)* The polytope $PEDC_n = EDC_{KN_n} \cap \{\delta : \delta(1,n) \le 1\}$ is affinely isomorphic, preserving the vertex lattice, to the Chan–Robbins–Yuen polytope $CRY_n$ (a face of the Birkhoff polytope); hence the two have the same Ehrhart series and normalized volume, $\mathrm{Vol}(CRY_n) = \prod_{i=1}^{n-2} \mathrm{Cat}(i)$.

## Expansion

Equidistant split networks generalize ultrametric trees: an equidistant tree metric is one where all leaves are equally far from the root, and the cone of ultrametrics on a fixed tree is a face of the space of equidistant circular metrics. The left and right inequalities say distances from the two extreme leaves grow along the circle, the covering inequalities are the Kalmanson conditions that remain irredundant once equidistance is imposed, and faces arise by setting split weights to zero. Matching the cross-section to the Chan–Robbins–Yuen flow polytope transfers its known volume formula, a product of Catalan numbers, to these phylogenetic network spaces.

## Sources

- Bryson Kagy and Seth Sullivant, "Equidistant Circular Split Networks", SIAM Journal on Applied Algebra and Geometry 9 (2025), 1–32, <https://doi.org/10.1137/24m1642263>; numbering as in arXiv:2402.11032: Theorem 3.8 (Kalmanson), Theorem 4.1, Corollary 4.8 and Theorem 6.2.
