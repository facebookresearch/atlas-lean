# Characteristic kernels

Let $X$ be a measurable space and $H$ a real reproducing kernel Hilbert space of functions on $X$ with feature map $\varphi$. The kernel of $H$ is characteristic if the mean embedding is injective on the probability measures for which $\varphi$ is Bochner integrable: for such probability measures $P$ and $Q$, $\mu_P = \mu_Q$ implies $P = Q$. Equivalently, the maximum mean discrepancy between such probability measures vanishes only when they are equal.

## Idea

A characteristic kernel is one whose mean embedding loses no information about a distribution, so that the maximum mean discrepancy is a metric on the probability measures concerned and a two-sample test based on it can detect every difference. The linear kernel on $\mathbb{R}$ is not characteristic: its embedding sees only the mean. Two sufficient conditions are standard. On a compact metric space, a continuous kernel whose RKHS is dense in the continuous functions (a universal kernel) is characteristic. On $\mathbb{R}^d$, a bounded continuous translation-invariant kernel $\psi(x - y)$ is characteristic exactly when the spectral measure of $\psi$ has full support; this covers the Gaussian and Laplacian kernels and excludes the sinc kernel.

## Statements

- [Characteristic kernel](is-characteristic.md)
- [The MMD of a characteristic kernel separates probability measures](mmd-eq-zero-iff-of-is-characteristic.md): basic property: the MMD separates laws
- [Universal kernels are characteristic](is-characteristic-of-universal.md): universal kernels are characteristic
- [The MMD of a universal kernel characterizes distributions](mmd-eq-zero-iff-of-universal.md): consequence for universal kernels
- [Characterization of characteristic translation-invariant kernels](is-characteristic-iff-support-eq-univ.md): criterion for translation-invariant kernels

## Background

- [Kernel mean embedding](../kernel-mean-embedding/README.md)
- [Maximum mean discrepancy](../maximum-mean-discrepancy/README.md)

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*, Journal of Machine Learning Research (2012).
