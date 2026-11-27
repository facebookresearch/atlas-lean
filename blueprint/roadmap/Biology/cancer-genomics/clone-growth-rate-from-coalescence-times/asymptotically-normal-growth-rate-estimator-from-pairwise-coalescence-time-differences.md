# Asymptotically normal growth-rate estimator from pairwise coalescence-time differences

**Setting.** A supercritical birth–death process with net growth rate $r>0$ (for example a cancer clone) is sampled at time $T$. For a sample of $n$ individuals, the genealogy is described by $n-1$ coalescence times $H_{1,n},\dots,H_{n-1,n}$; in practice these are reconstructed from DNA sequences. In the large-$T$ limit the coalescent point process representation gives

$$H_{i,n}=T-\frac1r\big(\log Q_n+U_{i,n}\big),$$

with $U_{i,n}$ i.i.d. standard logistic and $Q_n$ a common random factor. Pairwise differences $H_{i,n}-H_{j,n}=(U_{j,n}-U_{i,n})/r$ therefore do not depend on the unknown $T$ and $Q_n$. Consider estimators of the form

$$\hat r=\frac{c(n)\,(n-1)(n-2)}{\sum_{i=1}^{n-1}\sum_{j=1}^{n-1}(H_{i,n}-H_{j,n})^+}.$$

Here $c(n)$ is chosen to minimize mean squared error ($\hat r_{MSE}$), to make $\hat r$ unbiased ($\hat r_{Bias}$), or to make $1/\hat r$ unbiased for $1/r$ ($\hat r_{Inv}$).

**Theorem.**

1. In the $T=\infty$ representation,

$$\sqrt n\,(\hat r-r)\Rightarrow\mathcal N\Big(0,\ r^2\Big(4-\frac{\pi^2}{3}\Big)\Big).$$

2. If the sampling time $T_n$ grows fast enough that $n^{3/2}(\log n)\,e^{-rT_n}\to0$, then for coalescence times of a sample from the birth–death process at time $T_n$,

$$\sqrt n\,(\hat r_{Inv}-r)\Rightarrow\mathcal N\Big(0,\ r^2\Big(4-\frac{\pi^2}{3}\Big)\Big).$$

## Proof sketch

The expected total internal branch length, conditional on the coalescence times, is dominated by $\frac1{n-1}\sum_{i,j}(H_{i,n}-H_{j,n})^+$. This motivates an estimator inversely proportional to the average positive pairwise difference. The quantity $1/\hat r$ is a U-statistic of the i.i.d. logistic variables with symmetric kernel $\tfrac12|U_i-U_j|/r$, so Hoeffding's theorem gives asymptotic normality. Its variance can be computed from logistic moments; this is where $\pi^2/3$, the variance of the logistic law, comes from. The delta method then transfers the result to $\hat r$. A coupling between finite-$T_n$ and limiting coalescence times shows that the difference is $o_p(n^{-1/2})$ under the growth condition on $T_n$. Earlier closed-form estimators based on internal and external branch lengths come from large-$n$ asymptotics and perform poorly in small samples. This estimator is built for that regime: it is computationally cheap, comes with confidence intervals, and is evaluated by simulation for small $n$.

## Sources

- Carola Sophia Heinzel and Jason Schweinsberg, "Estimating the Growth Rate of a Birth and Death Process Using data From a Small Sample", *Bulletin of Mathematical Biology* 88 (2026), 72, <https://doi.org/10.1007/s11538-026-01626-2>. Preprint version: arXiv:2508.16110 (2025), Section 2 (estimator family and choices of $c(n)$), the lemma on asymptotic normality of $\hat r$ in the limiting model, Section 2.5 (confidence intervals), Theorem 1 (asymptotic normality of $\hat r_{Inv}$ at finite sampling times), appendix (derivation of the conditional internal length), <https://doi.org/10.48550/arXiv.2508.16110>.
