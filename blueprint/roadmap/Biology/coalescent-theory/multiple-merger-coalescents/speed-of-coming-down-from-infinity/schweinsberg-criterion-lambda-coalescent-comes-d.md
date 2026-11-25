# Schweinsberg's criterion for coming down from infinity

Let $\Lambda$ be a nonzero finite measure on $[0,1]$ with
$\Lambda(\{1\})=0$. For the
[Λ-coalescent on the natural numbers](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)
started from singletons, let $\gamma_b>0$, $b\ge2$, be the
[block-count drift](../block-count-drift-of-coalescents/block-drift.md).
It comes down from infinity, meaning almost surely finitely many blocks
at every positive time, if and only if

$$\sum_{b=2}^\infty\gamma_b^{-1}<\infty.$$

Otherwise it has infinitely many blocks at every positive time almost
surely. The series criterion is also equivalent to [Grey's condition](grey-condition.md)
for its [Laplace exponent](psi.md).
For unit-rate Kingman, $\gamma_b=\binom b2$ and the inverse-drift sum is two.
For the Bolthausen--Sznitman coalescent with uniform $\Lambda$,
$\gamma_b=b\sum_{k=2}^b1/k\sim b\log b$, so the sum diverges and it stays
infinite. The Beta$(2-\alpha,\alpha)$ coalescent, $0<\alpha<2$, comes down
if and only if $\alpha>1$.
The excluded zero measure has no mergers; treating its real reciprocals
as zero would give a false criterion.

## Depends on

- [Block-count drift](../block-count-drift-of-coalescents/block-drift.md)
- [The Λ-coalescent on the natural numbers](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)
- [Grey's condition](grey-condition.md)
- [The Laplace exponent](psi.md)

## Proof depends on

- [Sufficiency](sufficiency-sum-1-gamma-b-infinity-implies-comin.md)
- [Necessity](necessity-coming-down-from-infinity-implies-sum.md)
- [Entrance dichotomy and finite expected absorption](entrance-dichotomy-and-finite-expected-absorption.md)
- [Integral form of the block-count drift](../block-count-drift-of-coalescents/block-drift-eq-integral.md)
- [Kingman's drift](../block-count-drift-of-coalescents/block-drift-dirac-zero.md)
- [The uniform-measure drift](../block-count-drift-of-coalescents/block-drift-volume.md)

## Expansion

The two implications follow from the sufficiency and necessity lemmas,
and the almost-sure alternative uses the separate entrance dichotomy.
For the analytic equivalence, the drift kernel for $x>0$ is
$[bx-1+(1-x)^b]/x^2$, while the Laplace kernel is
$[bx-1+e^{-bx}]/x^2$. Their values at zero are $b(b-1)/2$ and $b^2/2$.
For every integer $b\ge4$,

$$\tfrac12e^{-2}\psi(b)\le\gamma_b\le\psi(b).$$

For the upper bound use $(1-x)^b\le e^{-bx}$. For the lower bound,
if $bx\ge2$, the drift numerator is at least $bx/2$, at least half
the Laplace numerator. If $bx\le2$, the second derivative of the drift
numerator on $[0,x]$ is at least $b(b-1)e^{-2}$, since
$(1-2/b)^{b-2}\ge e^{-2}$; integrate twice and use the Laplace numerator
bound $(bx)^2/2$. The limits at zero satisfy the same comparison.
Integration proves the display. The positive function $\psi(q)$ is
nondecreasing for $q>0$, so the integral test makes
$\sum_b1/\psi(b)<\infty$ equivalent to integrability of $1/\psi$ on a
positive tail. Bounded intervals away from zero cause no additional
integrability issue. This proves the Grey equivalence without interpreting
a divergent nonnegative integral as the real-valued tail function.

For the Beta examples, the density is a positive constant times
$x^{1-\alpha}(1-x)^{\alpha-1}$. If $0<\alpha<1$, its $x^{-1}$ integral is
finite, and $\gamma_b\le b\int x^{-1}\Lambda(dx)$, forcing divergence.
At $\alpha=1$ use the uniform-measure formula. If $1<\alpha<2$, integration
over $[2/b,3/b]$ for $b\ge6$ gives $\gamma_b\ge c_\alpha b^\alpha$ for
some $c_\alpha>0$: the drift numerator is at least one there, and the
density has the stated power near zero. Thus the inverse-drift sum
converges. These arguments do not require an unproved exact asymptotic
constant for the Beta drift.

## Sources

- J. Schweinsberg, "A necessary and sufficient condition for the Λ-coalescent to come down from infinity", Electronic Communications in Probability 5 (2000), 1--11, <https://www.maths.tcd.ie/EMIS/journals/EJP-ECP/article/download/1013/1013-3391-1-PB.pdf>, Theorem 1 and its standing no-atom-at-one assumption on p. 2; Lemmas 6--9; Example 15 on p. 10.
- N. Berestycki, *Recent progress in coalescent theory* (2009), <https://arxiv.org/abs/0909.3985>, Section 3.1.5, Theorems 3.6--3.7, Corollary 3.2 and the subsequent Grey-condition remark. The explicit uniform kernel comparison above supplies the analytic equivalence.
