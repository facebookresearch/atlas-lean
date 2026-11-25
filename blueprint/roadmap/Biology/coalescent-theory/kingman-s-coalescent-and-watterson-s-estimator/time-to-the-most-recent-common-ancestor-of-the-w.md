# Time to the most recent common ancestor of the whole population under Kingman’s coalescent

Let $(T_k)_{k \ge 2}$ be independent random variables on one probability space with
$T_k \sim \mathrm{Exp}\binom k2$, and put $T_{\mathrm{MRCA},n} = \sum_{k=2}^n T_k$, so that each
$(T_k)_{2 \le k \le n}$ is a [family of Kingman holding times](kingman-times.md). Then
$T_{\mathrm{MRCA},n}$ increases almost surely to $T_\infty = \sum_{k \ge 2} T_k < \infty$, and

$$\mathbb E\, T_\infty = 2, \qquad \operatorname{Var} T_\infty = \frac{4\pi^2}{3} - 12 \approx 1.1595 .$$

Indeed $\mathbb E\, T_{\mathrm{MRCA},n} = 2(1 - 1/n)$ and
$\operatorname{Var} T_{\mathrm{MRCA},n} = \sum_{k=2}^n \binom k2^{-2}$, and
$\sum_{k \ge 2} \binom k2^{-2} = 4 \sum_{k \ge 2} \bigl(\tfrac{1}{k-1} - \tfrac1k\bigr)^2 = 4\bigl(2\zeta(2) - 3\bigr) = \tfrac{4\pi^2}{3} - 12$.
The common probability space matters: for independent families of holding times chosen separately for
$n = 2$ and $n = 3$, $\mathbb P(T_{\mathrm{MRCA},3} < T_{\mathrm{MRCA},2}) = 3/8 > 0$, so separate finite-sample instances do not imply a nondecreasing coupling. Indeed this probability is $E[e^{-(T_2^{(3)}+T_3^{(3)})}]=(1/2)(3/4)$ when the two families are independent. The
law of $T_\infty$ is the law of the time until [Kingman's coalescent on $\mathbb N$](../partition-valued-kingman-coalescent/kingman-s-coalescent-comes-down-from-infinity.md) has one
block.

## Depends on

- [Kingman holding times](kingman-times.md)

## Proof depends on

- [Expected time to the most recent common ancestor](integral-tmrca.md)
- [Variance of the time to the most recent common ancestor](variance-tmrca.md)
- [Kingman's coalescent comes down from infinity](../partition-valued-kingman-coalescent/kingman-s-coalescent-comes-down-from-infinity.md): the infinite-genealogy identification in law, separate from the auxiliary partial-sum coupling.

## Expansion

A sound expansion uses monotone convergence for the mean and the independence of the $T_k$ (or
$L^2$ convergence of the partial sums) for the variance. For the final identification, the restriction times $M_n$ of the infinite coalescent increase to its whole-population time, while each $M_n$ has the law of $T_{\mathrm{MRCA},n}$; taking distributional limits identifies the two limits without equating their finite-sample couplings.

## Sources

- S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population genetics models", Theoretical Population Biology 26 (1984), 119–164, <https://doi.org/10.1016/0040-5809(84)90027-3>, Section 6 (as $i \to \infty$ the expected time to a single ancestor is $2$ and the variance is $4\pi^2/3 - 12 \approx 1.16$, attributed there to Watterson (1982)).
