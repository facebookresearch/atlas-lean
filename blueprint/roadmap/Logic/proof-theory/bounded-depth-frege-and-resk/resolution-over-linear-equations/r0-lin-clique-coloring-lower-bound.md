# Interpolation and clique-coloring lower bounds for R$^0$(lin)

R$^0$(lin) has polynomial upper bounds on interpolant circuits, and its refutations of the clique-coloring formulas need size $2^{\Omega(n^{\epsilon})}$ for $k'=k-1$ and $k\sqrt k\approx n/\log n$, and $n^{\Omega(\log n/\sqrt{\log\log n})}$ for $k=\sqrt n$ and $k'=(\log n)^2/(8\log\log n)$.

**Interpolation.** For disjoint variable vectors $\vec p$ ($n$ variables), $\vec q$, $\vec r$ and collections $A_1(\vec p,\vec q),\dots,A_k(\vec p,\vec q)$ and $B_1(\vec p,\vec r),\dots,B_\ell(\vec p,\vec r)$, let $\mathcal U_A$ be the set of $u\in\{0,1\}^n$ that extend to a common satisfying assignment of all $A_i$, and $\mathcal V_B$ the analogous set for the $B_j$. A refutation system $\mathcal P$ has *polynomial upper bounds on interpolant circuits* if, whenever $\bigwedge_iA_i\wedge\bigwedge_jB_j$ has a $\mathcal P$-refutation of size $S$, there is a Boolean circuit of size polynomial in $S$ that outputs $1$ on $\mathcal U_A$ and $0$ on $\mathcal V_B$.

**Theorem.** [R$^0$(lin)](r0-lin-fragment.md) has polynomial upper bounds on interpolant circuits.

**Clique-coloring.** The formulas $\mathrm{CLIQUE}^n_{k,k'}$ have edge variables $p_{i,j}$, variables $q_{\ell,i}$ placing vertex $i$ as the $\ell$-th vertex of a $k$-clique, and variables $r_{t,i}$ placing vertex $i$ in colour class $t\le k'$; their clauses say that the $q$'s pick $k$ distinct vertices that are pairwise adjacent, and that the $r$'s properly colour every vertex with one of $k'$ colours, so adjacent vertices get different colours. For $k'<k$ they are unsatisfiable.

**Corollary.** (i) Let $3\le k'=k-1$ and $\tfrac12\cdot n/(8\log n)\le k\sqrt k\le n/(8\log n)$. Then for every $\epsilon<1/3$, every R$^0$(lin) refutation of $\mathrm{CLIQUE}^n_{k,k'}$ has size at least $2^{\Omega(n^{\epsilon})}$. (ii) For $k=\sqrt n$ and $k'=(\log n)^2/(8\log\log n)$, every R$^0$(lin) refutation of $\mathrm{CLIQUE}^n_{k,k'}$ has size at least $n^{\Omega(\log n/\sqrt{\log\log n})}$.

## Expansion

The set of assignments satisfying an R$^0$(lin)-line with $N$ variables has communication complexity $O(\log N)$ in the Karchmer-Wigderson-style task of Krajíček's interpolation theorem, because an R$^0$(lin)-line is a constant number of blocks of equations sharing one linear form with constant coefficients, plus one clause, and the players can evaluate each block by exchanging the values of their partial sums of that form. Krajíček's semantic interpolation then gives separating circuits of size $(m+n)2^{O(\log N)}$. For the lower bounds, a refutation with low-communication lines yields, by Bonet-Pitassi-Raz, a monotone circuit of size $m\cdot2^{3\zeta+1}$ computing a clique separator, and the [Alon-Boppana monotone lower bound](../../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md) for clique separators gives the stated sizes. The clique-coloring formulas are the standard hard instances for feasible interpolation, as in resolution and cutting planes.

## Depends on

- [The fragment R0(lin)](r0-lin-fragment.md)

## Proof depends on

- [Alon–Boppana monotone clique lower bound](../../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md)

## Sources

- Ran Raz and Iddo Tzameret, "Resolution over linear equations and multilinear proofs", *Annals of Pure and Applied Logic* 155, 2008, https://doi.org/10.1016/j.apal.2008.04.001; numbering as in arXiv:0708.1529v1 (Section 6.3, Definition 6.3; Section 7, Definitions 7.1-7.4, Theorem 23, Theorem 24, Lemma 25; Section 8, Definition 8.1, Theorems 26-27, Lemma 28, Corollaries 29 and 30).
