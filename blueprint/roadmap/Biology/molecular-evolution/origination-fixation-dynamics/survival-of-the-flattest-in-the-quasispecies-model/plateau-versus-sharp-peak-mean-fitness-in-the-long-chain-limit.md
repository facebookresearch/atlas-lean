# Survival of the flattest: plateau versus sharp peak in the long-chain quasispecies limit

**Model.** Genotypes are binary sequences $u \in E = \{0,1\}^\ell$ ($\ell$ even). Each site mutates independently with probability $q$ per replication, giving the mutation kernel $M(u,v) = q^{d(u,v)}(1-q)^{\ell-d(u,v)}$ with $d$ the Hamming distance. For a fitness function $f \ge 1$, the quasispecies distribution $x$ (Moran–Kingman model) solves

$$\lambda\, x(v) = \sum_{u\in E} x(u) f(u) M(u,v), \qquad \sum_v x(v) = 1,$$

where the mean fitness $\lambda = \sum_u f(u)x(u)$ is the Perron–Frobenius eigenvalue of $(f(u)M(u,v))$. The *long-chain regime* is $\ell \to \infty$, $q \to 0$, $\ell q \to a \in (0,\infty)$.

**Landscape.** For $\delta, \sigma \ge 1$ let

$$f_{\mathrm{SP/PL}}(u) = \begin{cases}\delta & u = 0\cdots0 \ \ (\text{sharp peak}),\\ \sigma & u \text{ has } \ell/2 \text{ zeros and } \ell/2 \text{ ones} \ \ (\text{plateau}),\\ 1 & \text{otherwise.}\end{cases}$$

**Theorem.** Assume $\sigma > 1$ and $\delta \ge 1$. Let $\lambda(a,\sigma)$ be the unique $\lambda > 1$ with

$$\frac{1}{\sigma-1} = \sum_{n\ge1}\frac{e^{-an}}{\lambda^n}\sum_{k\ge0}\frac{(an)^{2k}}{2^{2k}(k!)^2}.$$

In the long-chain regime, $\lambda_{\mathrm{SP/PL}} \to \max\big(\delta e^{-a}, \lambda(a,\sigma)\big)$. Writing $y(0)$ for the equilibrium frequency of $0\cdots0$ and $y(\ell/2)$ for the total equilibrium frequency of the plateau class:
- if $\lambda(a,\sigma) > \delta e^{-a}$, then $y(0) \to 0$ and $y(\ell/2) \to \dfrac{\lambda(a,\sigma)-1}{\sigma-1}$;
- if $\delta e^{-a} > \lambda(a,\sigma)$, then $y(\ell/2) \to 0$ and $y(0) \to \dfrac{\delta e^{-a}-1}{\delta-1}$.

Since $\lambda(a,\sigma)$ decreases more slowly in $a$ than $\delta e^{-a}$, for $\delta > \sigma$ there is a range of mutation rates where the lower but flatter plateau wins: *survival of the flattest*.

The case $\sigma = 1$ (a plateau no fitter than the background), which the landscape definition allows, is excluded: the defining equation divides by $\sigma - 1$, and its right-hand side is a positive finite series for every $\lambda > 1$, so no root $\lambda(a,1) > 1$ exists (for $\delta = \sigma = 1$ every fitness is $1$ and the mean fitness is exactly $1$ for every $\ell$).

## Depends on

- [Eigen's error threshold](../../../population-dynamics/eigen-s-quasispecies-error-threshold/master-equilibrium-exp-pos-iff.md)

## Expansion

For a nonneutral sharp peak alone ($\delta > 1$) the quasispecies has the series representation $x(u) = \sum_{n\ge1}\frac{\lambda-1}{\lambda^n}\mathbb{P}(X_n = u \mid X_0 = w^*)$ for the mutation Markov chain $X$, which yields the error threshold: $\lambda \to \max(1, \delta e^{-a})$. For the plateau, lumping genotypes by Hamming class reduces the problem to a Hamming-class Markov chain (a single step can change the class by more than one); in the long-chain limit the number of mutations per generation is Poisson$(a)$ and the class changes by the difference of two independent Poisson$(a/2)$ variables, whose return probability after $n$ generations is $e^{-an}I_0(an)$ with $I_0$ the modified Bessel function, giving the series defining $\lambda(a,\sigma)$. Monotonicity of the Perron eigenvalue in the matrix entries gives $\liminf \lambda_{\mathrm{SP/PL}} \ge \max(\cdot,\cdot)$, and the lumped renewal equations give the matching upper bound and the limiting frequencies.

## Sources

- Maxime Berger and Raphaël Cerf, "Survival of the flattest in the quasispecies model", Adv. Appl. Probab. 57 (2025), 566–606, <https://doi.org/10.1017/apr.2024.39>. Numbering follows the arXiv version, arXiv:2306.09221 (2023): Theorem 1.9 (error threshold), Theorem 1.26 (sharp peak versus plateau, proved in Section 7) and Proposition 2.6 (series representation), <https://doi.org/10.48550/arXiv.2306.09221>.
