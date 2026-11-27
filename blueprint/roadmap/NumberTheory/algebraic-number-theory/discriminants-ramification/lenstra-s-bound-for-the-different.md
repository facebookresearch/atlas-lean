# Lenstra's bound for the different

Let $A$ be a discrete valuation ring of characteristic $0$ with fraction field $K$ and valuation
$\operatorname{ord}_A$, let $L/K$ be a finite field extension of degree $n$, and let $B$ be the
integral closure of $A$ in $L$. The different $\mathfrak{D}_{B/A}$ is the inverse of the fractional
ideal $\{x \in L : \operatorname{Tr}_{L/K}(xB) \subset A\}$; it is an integral ideal. Suppose that
$B$ is a discrete valuation ring of ramification index $e$ over $A$. Then the valuation $r$ of
$\mathfrak{D}_{B/A}$ on $B$ satisfies

$$r \le e - 1 + e \cdot \operatorname{ord}_A(n).$$

No separability of the residue field extension is assumed. When it is separable this follows from
the remark after Serre's Proposition III.6.13 (Dedekind's discriminant bound), as Javanpeykar
notes; the general case is needed for imperfect residue fields. The proof takes a uniformizer $x$ of $A$
and $y = 1/(nx) \in K$: the trace of $y$ is $1/x \notin A$, so $\mathfrak{D}_{B/A}^{-1}
\subsetneq yB$, hence $\mathfrak{D}_{B/A} \supsetneq (nx)$ and $r < \operatorname{ord}_B(nx) = e
(\operatorname{ord}_A(n) + 1)$.

## Depends on

None among the pages; the different is in Mathlib.

## Proof depends on

None among the pages.

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, §4.1, Proposition 4.1.1 (attributed to H. W. Lenstra, Jr.) and Remark 4.1.2,
  pp. 112–113.
