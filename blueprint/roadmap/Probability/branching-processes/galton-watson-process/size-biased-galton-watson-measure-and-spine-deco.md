# The size-biased Galton–Watson tree and its spine

Let $p_k=\mathbb P(L=k)$ be an offspring law on $\mathbb N$ with
$0<m=\mathbb EL<\infty$. Work on the
[labelled and marked tree spaces](ulam-harris-labelled-galton-watson-trees-and-pro.md),
with ordinary tree law $P=\mathrm{GW}$, finite-level sigma-fields
$\mathcal F_n$, and [martingale](galton-watson-martingale-w-n-z-n-m-n.md)
$W_n=Z_n/m^n$.
The size-biased offspring law is $\mathbb P(\widehat L=k)=kp_k/m$.

There exists a marked-tree law $Q_*$ obtained by giving each successive
spine vertex an independent $\widehat L$ number of children, choosing one
uniformly to continue the spine, and giving every nonspine child an
independent ordinary Galton–Watson descendant tree. All these choices are
independent except for the displayed parent-child construction.
For a finite truncation $t$ and a vertex $v$ at level $n$,

$$Q_*([t;v]_n)=m^{-n}P([t]_n),\qquad
 Q|_{\mathcal F_n}=W_nP|_{\mathcal F_n},$$

where $Q$ forgets the mark. Conditional on the unmarked first $n$ levels,
the spine vertex at level $n$ is uniform on its $Z_n$ vertices,
$Q_*$-almost surely. Such levels are nonempty since $\widehat L\ge1$.
The off-spine count $Z_n-1$ starts at zero and has Galton–Watson reproduction
with immigration $Y_n=\widehat L_n-1$ at level $n\ge1$.
The immigration sequence is iid and independent of all off-spine
reproduction. The distinguished individual itself is not an immigrant.

## Depends on

- [Labelled and marked Galton–Watson trees](ulam-harris-labelled-galton-watson-trees-and-pro.md)
- [The Galton–Watson martingale](galton-watson-martingale-w-n-z-n-m-n.md)

## Proof depends on

- [Kolmogorov extension theorem](../../foundations/kolmogorov-extension-theorem/kolmogorov-extension.md)

## Expansion

Generate countably many independent offspring and uniform choices, then
apply the measurable tree construction. At a spine vertex with $k$
children, the size bias $k/m$ and uniform factor $1/k$ cancel. Multiplying
along $n$ spine vertices yields $m^{-n}$ times the ordinary cylinder
probability. Sum over the $Z_n(t)$ possible marks to obtain the unmarked
density, and divide to obtain uniformity of the mark on positive-probability
cylinders. For an arbitrary measurable finite-level event, sum the
countably many such cylinder identities.

The unmarked densities have total mass $\mathbb E_PW_n=1$ and are
projective because $\mathbb E_P[W_{n+1}\mid\mathcal F_n]=W_n$.
The off-spine children of the previous spine vertex are precisely the
new immigrants, giving the asserted immigration recursion.
All these statements hold for $0<m<\infty$; supercriticality is required
only for the later growth and Kesten--Stigum conclusions.

## Sources

- R. Lyons and Y. Peres, *Probability on Trees and Networks*, corrected edition of August 19, 2026, <https://rdlyons.pages.iu.edu/prbtree/book.pdf>, Section 12.1, equations (12.1)--(12.3), Figure 12.1, Exercise 12.5 and the off-spine immigration discussion.
