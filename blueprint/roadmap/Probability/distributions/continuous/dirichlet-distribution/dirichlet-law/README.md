# Dirichlet distribution

Let $n \in \mathbb{N}$ and $\alpha = (\alpha_0, \dots, \alpha_n) \in \mathbb{R}^{n+1}$. On $\mathbb{R}^n$, let $D_\alpha(x) = \bigl(\prod_{i=0}^{n-1} x_i^{\alpha_i - 1}\bigr)\bigl(1 - \sum_{i=0}^{n-1} x_i\bigr)^{\alpha_n - 1}$ when $x_i > 0$ for every $i$ and $\sum_{i=0}^{n-1} x_i < 1$, and $D_\alpha(x) = 0$ otherwise (the unnormalized Dirichlet density), and let $B(\alpha) = \prod_{i=0}^{n} \Gamma(\alpha_i) / \Gamma\bigl(\sum_{i=0}^{n} \alpha_i\bigr)$ be the multivariate beta function. The Dirichlet distribution $\mathrm{Dir}(\alpha)$ is the measure on $\mathbb{R}^{n+1}$ obtained by pushing forward the measure on $\mathbb{R}^n$ with density $D_\alpha / B(\alpha)$ with respect to Lebesgue measure along $x \mapsto (x_0, \dots, x_{n-1}, 1 - \sum_{i=0}^{n-1} x_i)$. The quotient is taken in $[0, \infty]$ with a nonpositive $B(\alpha)$ read as $0$, which matters only when some $\alpha_i \le 0$. For positive parameters $\mathrm{Dir}(\alpha)$ is a probability measure concentrated on the vectors with positive entries summing to $1$.

## Idea

For positive parameters the Dirichlet law is a law on probability vectors, that is, on random proportions of $n + 1$ categories. For two categories it is the law of $(X, 1 - X)$ with $X$ beta-distributed. Since the last coordinate is $1$ minus the sum of the others, the density lives on the first $n$ coordinates. It is normalised by the Dirichlet integral $\int D_\alpha = B(\alpha)$ for positive parameters, proved by induction: the substitution $x = (t, (1 - t)u)$ splits off the first coordinate and leaves a beta integral in $t$. The mean of $\theta_i$ is $\alpha_i / \sum_j \alpha_j$. In Bayesian statistics it is the conjugate prior of the multinomial law: weighting $\mathrm{Dir}(\alpha)$ by the likelihood $\prod_i \theta_i^{k_i}$ of observed counts $k$ gives $\mathrm{Dir}(\alpha + k)$ up to the constant $B(\alpha + k)/B(\alpha)$. The flat case $\alpha = (1, \dots, 1)$ is the uniform law on the simplex.

## Statements

- [Dirichlet distribution](dirichlet-measure.md)
- [Unnormalized Dirichlet density](dirichlet-density.md): definition used in the main definition
- [Multivariate Beta function](multi-beta.md): definition used in the main definition (normalising constant)
- [Simplex completion](simplex-completion.md): definition used in the main definition
- [The Dirichlet integral](lintegral-dirichlet-density.md): the Dirichlet integral, which normalises the law
- [The Dirichlet integral for a single parameter](lintegral-dirichlet-density-zero.md): lemma: base case of the Dirichlet integral
- [Splitting off the first coordinate of the Dirichlet density](dirichlet-density-cons-smul.md): lemma used in the proof of the Dirichlet integral
- [The Beta integral](lintegral-ioo-rpow-mul-rpow.md): lemma: the beta integral, used for the Dirichlet integral
- [Tonelli's theorem for the first coordinate](lintegral-fin-succ.md): lemma: Tonelli step, used for the Dirichlet integral and for weighted sums of a flat Dirichlet vector
- [Scaling the variable of a Lebesgue integral](lintegral-comp-smul-fin.md): lemma: change of scale, used for the Dirichlet integral and for weighted sums of a flat Dirichlet vector
- [The Dirichlet distribution is concentrated on the open simplex](ae-dirichlet-measure.md): basic property: concentration on the open simplex
- [Mean of the Dirichlet distribution](lintegral-dirichlet-measure-apply.md): basic property: the mean
- [Dirichlet–multinomial conjugacy](with-density-prod-pow-dirichlet-measure.md): Dirichlet–multinomial conjugacy, also used to compute the mean
- [Multiplying the Dirichlet density by a multinomial likelihood](dirichlet-density-mul-prod-pow.md): lemma used for Dirichlet–multinomial conjugacy

## Background

- [Moments of the beta distribution](../../beta-distribution/README.md)
