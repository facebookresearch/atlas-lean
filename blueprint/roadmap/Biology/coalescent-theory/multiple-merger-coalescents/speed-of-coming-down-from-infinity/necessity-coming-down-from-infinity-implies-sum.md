# Necessity in Schweinsberg's criterion

Let $\Lambda$ be a nonzero finite measure on $[0,1]$ with
$\Lambda(\{1\})=0$. Let $\gamma_b$ be its
[block-count drift](../block-count-drift-of-coalescents/block-drift.md),
which is positive for $b\ge2$. If the
[Λ-coalescent on the natural numbers](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)
started from singletons comes down from infinity, then

$$\sum_{b=2}^{\infty}\gamma_b^{-1}<\infty.$$

Equivalently, divergence of that sum implies that the coalescent has
infinitely many blocks at every positive time almost surely.

## Depends on

- [Block-count drift](../block-count-drift-of-coalescents/block-drift.md)
- [The Λ-coalescent on the natural numbers](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)

## Proof depends on

- [The drift is nondecreasing](../block-count-drift-of-coalescents/block-drift-mono.md)
- [Entrance dichotomy and finite expected absorption](entrance-dichotomy-and-finite-expected-absorption.md)
- [The absorption-time drift identity](sufficiency-sum-1-gamma-b-infinity-implies-comin.md)

## Expansion

First suppose the nonzero measure is supported on $[0,1/2]$. A chain
started above $2^l$ first enters $\{1,\ldots,2^l\}$ in its upper half
$\{2^{l-1}+1,\ldots,2^l\}$ with probability at least $1/2$.
To see this, at a pre-jump count $b>2^l$, pair a lower-half landing
$i+1$, $0\le i<2^{l-1}$, with the upper-half landing $i'+1$, where
$i'=2^l-1-i$. Their rate integrands are
$\binom bi x^{b-i-2}(1-x)^i$ and
$\binom b{i'}x^{b-i'-2}(1-x)^{i'}$, respectively. The second is at least
the first: $\binom bi\le\binom b{i'}$ and
$((1-x)/x)^{i'-i}\ge1$ for $0<x\le1/2$, with the inequality at zero
read by continuity. Integrate, sum the pairs, and condition on the count
just before first entrance. A chain started in that upper half visits it
with probability one.

For a restriction started at $n=2^m$, let $D_l$ denote the event that
some visited count lies in $\{2^{l-1}+1,\ldots,2^l\}$. Let $L_n(j)$
be the smallest visited count at least $j$, for $2\le j\le n$.
The absorption-time drift identity gives
$\mathbb E T_n=\sum_{j=2}^n\mathbb E[\gamma_{L_n(j)}^{-1}]$.
On $D_{l+1}$, $L_n(j)\le2^{l+1}$ for
$2^{l-1}<j\le2^l$. Hence, for $m\ge2$,

$$\mathbb E T_{2^m}\ge\frac18\sum_{l=1}^{m-1}
 \frac{2^{l+1}}{\gamma_{2^{l+1}}}.$$

For a nondecreasing positive $\gamma$, divergence of
$\sum_b\gamma_b^{-1}$ implies divergence of the displayed dyadic sum:
$\sum_{j=2^r}^{2^{r+1}-1}\gamma_j^{-1}\le2^r/\gamma_{2^r}$.
Thus $\mathbb E T_\infty=\infty$, and the entrance/absorption dichotomy
shows that this truncated-measure coalescent stays infinite.

For general $\Lambda$, put $\mu=\Lambda|_{[0,1/2]}$ and
$\nu=\Lambda|_{(1/2,1]}$. Nonnegative merger rates give
$\gamma_b^\mu\le\gamma_b^\Lambda$. If $\mu\ne0$, a divergent inverse-drift
sum for $\Lambda$ is therefore divergent for $\mu$, so the preceding
argument applies. If $\mu=0$, its coalescent simply never merges; no real
reciprocal $1/0$ is used to infer divergence.
The additional Poisson events from $\nu$ have finite rate
$c=\int_{(1/2,1]}x^{-2}\Lambda(dx)\le4\Lambda([0,1])$.
For any fixed $t>0$, with probability $e^{-ct}>0$ there is no such event
before $t$, and the full coalescent still has infinitely many blocks at $t$.
Its dichotomy, using $\Lambda(\{1\})=0$, implies that it stays infinite
almost surely. This proves the contrapositive.

## Sources

- J. Schweinsberg, "A necessary and sufficient condition for the Λ-coalescent to come down from infinity", Electronic Communications in Probability 5 (2000), 1--11, <https://www.maths.tcd.ie/EMIS/journals/EJP-ECP/article/download/1013/1013-3391-1-PB.pdf>, Lemmas 7--9, equations (13)--(16), pp. 6--7. The earlier finite-expectation step is Proposition 5, not the dyadic argument itself.
