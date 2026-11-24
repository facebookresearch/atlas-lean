# The Kesten–Stigum theorem

Start a Galton–Watson tree from one root with offspring law $L$ on
$\mathbb N$, mean $1<m<\infty$, and
[extinction probability](extinction-prob.md) $q<1$.
Let $W$ be the almost-sure [limit of $Z_n/m^n$](galton-watson-martingale-w-n-z-n-m-n.md)
under its ordinary law $P$. With $0\log^+0=0$, the following are equivalent:

1. $\mathbb P(W=0)=q$;
2. $\mathbb EW=1$;
3. $\mathbb E[L\log^+L]<\infty$.

If these fail, $W=0$ almost surely, including on survival. Thus a finite
supercritical mean alone does not guarantee positive normalized growth
on survival.

## Depends on

- [The Galton–Watson martingale and limit](galton-watson-martingale-w-n-z-n-m-n.md)
- [Extinction probability](extinction-prob.md)

## Proof depends on

- [The size-biased tree](size-biased-galton-watson-measure-and-spine-deco.md)
- [Martingale-density decomposition](dichotomy-lemma-for-a-nonnegative-martingale-den.md)
- [Size-biased tree growth](spine-growth-lemma-log-moment-controls-w-n-under.md)
- [Extinction criterion](extinction-prob-eq-one-iff.md)

## Expansion

Use the globally defined $\overline W=\limsup_nW_n$ under both tree laws.
The size-biased law has $Q|_{\mathcal F_n}=W_nP|_{\mathcal F_n}$ and the
finite-level sigma-fields generate the tree sigma-field. If the LlogL
moment is finite, size-biased growth makes $\overline W<\infty$
$Q$-almost surely, and the density decomposition gives $\mathbb E_PW=1$.
If it is infinite, $\overline W=\infty$ $Q$-almost surely, and the same
lemma gives $W=0$ $P$-almost surely. These are the two extreme cases here
because of the growth theorem, not because the general density lemma
excludes mixed measures.

Since $\mathbb P(W=0)\in\{q,1\}$ and $q<1$, expectation one implies
condition 1, while the infinite-moment case violates both conditions 1
and 2. This proves all three equivalences.

Poisson offspring of mean $m>1$ satisfies the moment condition because
$k\log k\le k^2$ for integers $k\ge1$ and its second moment is finite.
For an explicit failure example, put
$p_{2^j}=1/(j^2 2^j)$ for $j\ge1$, put the remaining mass at zero, and
put zero mass elsewhere. These masses sum to less than one,
$m=\sum_{j\ge1}j^{-2}\in(1,\infty)$, but

$$\mathbb E[L\log^+L]=\log2\sum_{j\ge1}j^{-1}=\infty.$$

Thus this is a supercritical law with positive survival probability yet
$W=0$ almost surely. It is not a finite truncation of a heavy tail used as
an argument for an infinite logarithmic moment.

## Sources

- R. Lyons and Y. Peres, *Probability on Trees and Networks*, corrected edition of August 19, 2026, <https://rdlyons.pages.iu.edu/prbtree/book.pdf>, Section 5.1, Kesten--Stigum statement and Corollary 5.7; Section 12.2, equations (12.5)--(12.7) and proof.
- R. Lyons, R. Pemantle and Y. Peres, "Conceptual proofs of L log L criteria for mean behavior of branching processes", Annals of Probability 23 (1995), 1125--1138, <https://doi.org/10.1214/aop/1176988176> (historical reference; the proof followed here is the textbook argument).
- H. Kesten and B. P. Stigum, "A limit theorem for multidimensional Galton--Watson processes", Annals of Mathematical Statistics 37 (1966), 1211--1223, <https://doi.org/10.1214/aoms/1177699266> (original reference).
