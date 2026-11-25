# Moment convergence of the number of blocks of a Λ-coalescent to the speed function

Let $\Lambda$ be a finite measure on $[0, 1]$ with $\Lambda(\{0\}) < \Lambda([0, 1])$ such that the
Λ-coalescent comes down from infinity, and let $N_t$ and $v$ be as in
[the almost sure asymptotics of the number of blocks](the-number-of-blocks-of-a-coalescent-is-asymptot.md). Then for every $d \in [1, \infty)$,

$$\lim_{s \downarrow 0} \mathbb E\Bigl[\,\sup_{0 < t \le s} \Bigl|\frac{N_t}{v(t)} - 1\Bigr|^d\,\Bigr] = 0 .$$

The case $d = 1$ already implies the almost sure statement: $X_s = \sup_{0 < t \le s} |N_t / v(t) - 1|$
decreases as $s \downarrow 0$, and by Fatou's lemma
$\mathbb E \lim_{s \downarrow 0} X_s \le \lim_{s \downarrow 0} \mathbb E X_s = 0$, so
$\lim_{s \downarrow 0} X_s = 0$ almost surely.

## Depends on

- [The number of blocks of a Λ-coalescent is asymptotic to the speed function](the-number-of-blocks-of-a-coalescent-is-asymptot.md)

## Expansion

A sound expansion follows the source proof of Theorem 2, which strengthens the martingale estimates used
for the almost sure statement. The hypothesis $\Lambda(\{0\}) < \Lambda([0, 1])$ is the source's standing
assumption that $\Lambda$ is not a multiple of $\delta_0$; the corresponding moment statement for
Kingman's coalescent is not part of this result.

## Sources

- J. Berestycki, N. Berestycki and V. Limic, "The Λ-coalescent speed of coming down from infinity", Annals of Probability 38 (2010), 207–233, <https://doi.org/10.1214/09-AOP475>, preprint <https://arxiv.org/abs/0807.4278>, Section 3, Theorem 2, equation (11); proof in Section 4.3.
