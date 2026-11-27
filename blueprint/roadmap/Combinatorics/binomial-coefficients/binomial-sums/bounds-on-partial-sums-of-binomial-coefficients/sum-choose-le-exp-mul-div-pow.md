# Partial binomial sums are at most $(eD/r)^r$

For natural numbers $r$ and $D$ with $1 \le r \le D$,

$$\sum_{j=0}^{r} \binom{D}{j} \le \Big(\frac{e D}{r}\Big)^{r}.$$

With $x = r / D \in (0, 1]$: $x^r \sum_{j \le r} \binom{D}{j} \le \sum_{j \le D} \binom{D}{j} x^j = (1 + x)^D \le e^{D x} = e^r$, which is the [exponential bound on a weighted partial binomial sum](pow-mul-sum-choose-le-exp.md) at that weight. It sharpens the [$(3D/r)^r$ bound](sum-choose-le-pow.md), since $e < 3$.

Combined with the Sauer–Shelah lemma, it bounds the number of labellings of $n$ points by a class of VC dimension $d$ with $1 \le d \le n$ by $(e n / d)^d$. Shalev-Shwartz and Ben-David state the bound for $m > d + 1$, that is for $r \le D - 2$; the inequality above holds for all $1 \le r \le D$.

## Informally uses

- [Exponential bound on a weighted partial binomial sum](pow-mul-sum-choose-le-exp.md): builds on, with the weight $x = r / D$.

## Background

- [Rademacher complexity of a VC class, explicit rate](../../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/rademacher-complexity/rademacher-complexity-sign-patterns-le-v.md): the learning-theory application, the rate $\sqrt{2 d \log(e n / d) / n}$.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Lemma 6.10 (Sauer–Shelah–Perles, with the bound $(e m / d)^d$ for $m > d + 1$) and Lemma A.5.
