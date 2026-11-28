# Asymptotically normal growth-rate estimator from pairwise coalescence-time differences

**Setting.** A supercritical birth–death process with net growth rate $r>0$ (for example a cancer clone) is sampled at time $T$. For a sample of $n$ individuals, the genealogy is described by $n-1$ coalescence times $H_{1,n},\dots,H_{n-1,n}$; in practice these are reconstructed from DNA sequences. In the large-$T$ limit the coalescent point process representation gives

$$H_{i,n}=T-\frac1r\big(\log Q_n+U_{i,n}\big),$$

where $Q_n$ is a common random factor with density $nq^{n-1}/(1+q)^{n+1}$ on $(0,\infty)$ and, given $Q_n=q$, the $U_{i,n}$ are i.i.d. with density

$$f_{U_{i,n}\mid Q_n=q}(u)=\frac{1+q}{q}\cdot\frac{e^u}{(1+e^u)^2},\qquad u\in(-\log q,\infty),$$

a standard logistic law conditioned on $(-\log q,\infty)$. Pairwise differences $H_{i,n}-H_{j,n}=(U_{j,n}-U_{i,n})/r$ therefore do not depend on the unknown $T$, although their law depends on $n$ through $Q_n$. A further limit $n\to\infty$ gives the representation $H_i=T-\frac1r\big(\log(1/W)+\log n+U_i\big)$ with $W$ exponential of mean $1$ and $U_1,\dots,U_{n-1}$ i.i.d. standard logistic, density $e^u/(1+e^u)^2$ on $\mathbb R$. Consider estimators of the form

$$\hat r=\frac{c(n)\,(n-1)(n-2)}{\sum_{i=1}^{n-1}\sum_{j=1}^{n-1}(H_{i,n}-H_{j,n})^+}.$$

Here $c(n)$ is chosen, for the first representation, to minimize mean squared error ($\hat r_{MSE}$), to make $\hat r$ unbiased ($\hat r_{Bias}$), or to make $1/\hat r$ unbiased for $1/r$ ($\hat r_{Inv}$); with $S_n=(n-1)(n-2)/\sum_{i,j}(U_{i,n}-U_{j,n})^+$ these are $c_{MSE}(n)=\mathbb E[S_n]/\mathbb E[S_n^2]$, $c_{Bias}(n)=1/\mathbb E[S_n]$ and

$$c_{Inv}(n)=\mathbb E\Big[\frac1{S_n}\Big]=\frac{n}{n-2}\Big(1-\frac1{n-1}\sum_{k=1}^{n-1}\frac1k\Big),$$

all tending to $1$ as $n\to\infty$.

**Theorem.**

1. In the second representation, with i.i.d. standard logistic $U_i$, the estimator with $c(n)=1$, $\hat r=(n-1)(n-2)\big/\sum_{i=1}^{n-1}\sum_{j=1}^{n-1}(H_i-H_j)^+$, satisfies

$$\sqrt n\,(\hat r-r)\Rightarrow\mathcal N\Big(0,\ r^2\Big(4-\frac{\pi^2}{3}\Big)\Big).$$

2. If the sampling time $T_n$ grows fast enough that $n^{3/2}(\log n)\,e^{-rT_n}\to0$, then for coalescence times of a sample from the birth–death process at time $T_n$,

$$\sqrt n\,(\hat r_{Inv}-r)\Rightarrow\mathcal N\Big(0,\ r^2\Big(4-\frac{\pi^2}{3}\Big)\Big).$$

## Proof sketch

The expected total internal branch length, conditional on the coalescence times, is dominated by $\frac1{n-1}\sum_{i,j}(H_{i,n}-H_{j,n})^+$. This motivates an estimator inversely proportional to the average positive pairwise difference. The quantity $1/\hat r$ is a U-statistic of the i.i.d. logistic variables with symmetric kernel $\tfrac12|U_i-U_j|/r$, so Hoeffding's theorem gives asymptotic normality. Its variance can be computed from logistic moments; this is where $\pi^2/3$, the variance of the logistic law, comes from. The delta method then transfers the result to $\hat r$. A coupling between finite-$T_n$ and limiting coalescence times shows that the difference is $o_p(n^{-1/2})$ under the growth condition on $T_n$. Earlier closed-form estimators based on internal and external branch lengths come from large-$n$ asymptotics and perform poorly in small samples. This estimator is built for that regime: it is computationally cheap, comes with confidence intervals, and is evaluated by simulation for small $n$.

## Sources

- Carola Sophia Heinzel and Jason Schweinsberg, "Estimating the Growth Rate of a Birth and Death Process Using data From a Small Sample", *Bulletin of Mathematical Biology* 88 (2026), 72, <https://doi.org/10.1007/s11538-026-01626-2>. Preprint version: arXiv:2508.16110 (2025), Section 2 (estimator family and choices of $c(n)$), the lemma on asymptotic normality of $\hat r$ in the limiting model, Section 2.5 (confidence intervals), Theorem 1 (asymptotic normality of $\hat r_{Inv}$ at finite sampling times), appendix (derivation of the conditional internal length), <https://doi.org/10.48550/arXiv.2508.16110>.
