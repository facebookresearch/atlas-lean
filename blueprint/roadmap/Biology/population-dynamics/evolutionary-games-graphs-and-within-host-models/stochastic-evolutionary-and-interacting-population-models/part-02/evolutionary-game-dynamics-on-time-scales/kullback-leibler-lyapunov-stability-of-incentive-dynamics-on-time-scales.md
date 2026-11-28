# Kullback–Leibler Lyapunov stability of incentive dynamics on time scales

**Incentive dynamics.** On the simplex $\Delta_n$, a game or evolutionary dynamic is described by an **incentive** $\varphi : \Delta_n \to \mathbb R^n$ through

$$x_i^{\Delta} = \varphi_i(x) - x_i\sum_{j=1}^n\varphi_j(x), \qquad i = 1,\dots,n,$$

where $x^\Delta$ is the time-scale (delta) derivative. On $\mathbb T = \mathbb R$ it is $\dot x$, and on $\mathbb T = h\mathbb Z$, $0 < h \le 1$, it is $(x(t+h) - x(t))/h$. Examples: the replicator incentive $\varphi_i = x_i(f_i(x) - \bar f(x))$, the best-reply incentive $\varphi_i = BR_i(x) - x_i$, and the logit incentive. For instance, $\varphi_i = x_if_i(x)/\bar f(x)$ with $\bar f = \sum_j x_jf_j > 0$ gives the continuous replicator equation (up to velocity) when $h \to 0$ and the discrete replicator map $x_i' = x_if_i(x)/\bar f(x)$ when $h = 1$.

An interior state $\hat x$ is an **incentive stable state (ISS)** if, for all $x \ne \hat x$ in a neighbourhood of $\hat x$,

$$\sum_i\frac{\hat x_i\,\varphi_i(x)}{x_i} > \sum_i\varphi_i(x).$$

For the replicator incentive this is exactly the evolutionarily stable state (ESS) condition $\hat x\cdot f(x) > x\cdot f(x)$.

**Theorem.**

1. (Time-scale Lyapunov function.) For $\mathbb T = h\mathbb Z$ with $0 \le h \le 1$ ($h = 0$ meaning $\mathbb T = \mathbb R$), the Kullback–Leibler divergence $D(x) = \sum_i\hat x_i\log(\hat x_i/x_i)$ is a local time-scale Lyapunov function for the incentive dynamic if and only if $\hat x$ is an ISS. Hence an interior ISS is locally asymptotically stable in both continuous and discrete time.
2. (ESS and payoff-positive dynamics.) Assume linear fitness, $f(x) = Ax$, and call an incentive **payoff positive** if $\varphi_i(x)/x_i - \sum_j\varphi_j(x) > 0 \iff f_i(x) > x\cdot f(x)$ for every $i$. Then an interior ESS is asymptotically stable for every smooth payoff-positive dynamic that has a nontrivial linearization at it (the source's Theorem 2, after Cressman; the source states that its results from this point on assume linear fitness). The source first normalizes the incentive and then states the condition without the sum: "Without loss of generality, we assume Σi ϕi(x) = 0 for every x ∈ ∆. ... the payoff positivity requirement, ϕi(x)/xi > 0 ⇔ fi(x) > x · f(x)". This page writes the condition for the normalized incentive $\varphi_i - x_i\sum_j\varphi_j$, which defines the same dynamic, so that it applies to every incentive; the unnormalized condition $\varphi_i(x)/x_i > 0 \iff f_i(x) > x\cdot f(x)$ would admit dynamics the source's theorem does not cover.
3. (Geometric generalization.) If the KL divergence is replaced by the divergence $D_G$ of a Riemannian metric $G$ on the simplex whose components have reciprocals that are escort functions (for example the Shahshahani metric), then $D_G$ is again a local time-scale Lyapunov function for the corresponding adaptive dynamics at an ESS. For several populations, each with its own metric and the same time scale, $\sum_\alpha D_{G_\alpha}(\hat x_\alpha\|x_\alpha)$ is a local Lyapunov function if and only if $\sum_\alpha\varphi_\alpha(x_\alpha)\cdot G_\alpha(x_\alpha)(\hat x_\alpha - x_\alpha) > 0$ near $\hat x$.

So the ESS stability theorem of replicator dynamics holds uniformly across continuous, discrete and mixed time scales, and across a family of information geometries.

## Expansion

For $h > 0$, $x_i' = x_i + h(\varphi_i - x_i\Phi)$ with $\Phi = \sum_j\varphi_j$, so $D(x') - D(x) = -\sum_i\hat x_i\log\bigl(1 + h(\varphi_i/x_i - \Phi)\bigr)$. Since $-\log(1+y) \ge -y$, with equality only at $y = 0$, this is $\le -h\bigl(\sum_i\hat x_i\varphi_i/x_i - \Phi\bigr)$, which is negative near $\hat x$ exactly under the ISS inequality. The case $h = 0$ is the classical computation $\dot D = -\bigl(\sum_i\hat x_i\varphi_i/x_i - \Phi\bigr)$. Escort and metric versions replace $\log$ by the escort logarithm $\int_1^x dv/e(v)$, and the same one-line inequality goes through.

## Sources

- Marc Harper, Dashiell E. A. Fryer, "Stability of Evolutionary Dynamics on Time Scales", arXiv (2012). Section 2 (incentive dynamics and ISS), Section 3 (Theorem 1), Section 4 (Theorem 2), Sections 6–8 (Theorems 3–6). <https://doi.org/10.48550/arXiv.1210.5539>. Published version: "Lyapunov Functions for Time-Scale Dynamics on Riemannian Geometries of the Simplex", Dynamic Games and Applications 5(3) (2015), 318–333, <https://doi.org/10.1007/s13235-014-0124-0>; locators above refer to the arXiv version.
