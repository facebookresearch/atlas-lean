# Final size equation for trait-structured epidemics

**Model.** Hosts carry a static trait $x$ in a measurable space $\Omega$, distributed according to a probability measure $\Phi$ in a population of size $N$. $A(\tau, x, \xi) \ge 0$ is the expected contribution to the force of infection on a host with trait $x$ from a host with trait $\xi$ infected $\tau$ time units ago. The fraction $s(t, x)$ of trait-$x$ hosts still susceptible satisfies the nonlinear renewal equation

$$s(t, x) = \exp\Big(-N\int_0^\infty\!\!\int_\Omega A(\tau, x, \xi)\,\big[1 - s(t - \tau, \xi)\big]\,\Phi(d\xi)\,d\tau\Big).$$

**Next-generation operator.** With $k_0(x, \xi) = \int_0^\infty A(\tau, x, \xi)\,d\tau$ bounded, the next-generation operator in terms of fractions is $(\mathcal K_0\psi)(x) = N\int_\Omega k_0(x, \xi)\psi(\xi)\,\Phi(d\xi)$, and $R_0$ is its spectral radius.

**Final size equation.** Since $s(\cdot, x)$ is nonincreasing, $s(\infty, x)$ exists. Writing $y = 1 - s(\infty, \cdot)$ for the attack-rate profile, it satisfies

$$y = F(y), \qquad F(y)(x) = 1 - e^{-(\mathcal K_0 y)(x)}.$$

$F$ is order preserving, and every solution $y \ge 0$ satisfies $y < 1$ pointwise.

**Hypotheses.** (H1) For every $\epsilon > 0$ there is $\delta > 0$ with $\int_\Omega|k_0(x_1, \xi) - k_0(x_2, \xi)|\,\Phi(d\xi) < \epsilon$ whenever $|x_1 - x_2| < \delta$. (H2) Some iterated kernel is uniformly positive: $\inf_{x,\xi}k^n(x, \xi) > 0$ for all $n \ge m$, where $k^1 = k_0$ and $k^{n+1}(x, \xi) = \int_\Omega k_0(x, \eta)k^n(\eta, \xi)\,\Phi(d\eta)$.

**Theorem.**

1. If $R_0 < 1$, the final size equation has only the trivial solution $y = 0$.
2. Under (H2), every nontrivial solution is strictly positive on $\Omega$.
3. If $\Omega$ is compact and (H1), (H2) hold, there is at most one nontrivial solution.
4. If $\Omega$ is compact, (H1), (H2) hold and $R_0 > 1$, there is exactly one nontrivial solution, and its values are bounded away from $0$ and $1$.

## Proof depends on

- [Subcritical decay](../../next-generation-operator-and-basic-reproduction/tendsto-norm-pow-apply-zero.md)
- [Krein–Rutman theorem for $C(K)$](../../../../Analysis/operator-theory/spectral-theory/krein-rutman.md)

## Depends on

- [The basic reproduction ratio `R₀`](../../next-generation-operator-and-basic-reproduction/generation-growth.md)

## Expansion

For $R_0 < 1$: since $1 - e^{-z} \le z$, a solution satisfies $y \le \mathcal K_0^n y$ for all $n$, and Gelfand's formula $\|\mathcal K_0^n\|^{1/n} \to R_0 < 1$ forces $\sup y = 0$. Positivity follows from $y \ge \big((1 - e^{-z_0})/z_0\big)^n\mathcal K_0^n y$ with $z_0 = \sup\mathcal K_0 y$, together with (H2). For uniqueness, take two nontrivial solutions $y, z$ and let $\theta = \min y/z$. If $\theta < 1$, strict concavity of $1 - e^{-u}$ gives $y(\bar x) > \theta z(\bar x)$ at the minimizer, a contradiction; by symmetry $y = z$. For existence, (H1) makes $\mathcal K_0$ compact on $C(\Omega)$ by Arzelà–Ascoli, and (H2) makes it strongly irreducible. The Krein–Rutman theorem then supplies a positive eigenvector $y_0$ for $R_0$, a small multiple of $y_0$ is a subsolution, and monotone iteration of $F$ converges uniformly to the solution.

## Sources

- Martin Bootsma, Danny Chan, Odo Diekmann and Hisashi Inaba, "The effect of host population heterogeneity on epidemic outbreaks", Mathematics in Applied Sciences and Engineering 5 (2024), 1–35, <https://doi.org/10.5206/mase/16718>; numbering as in arXiv:2308.06593v2: Section 2 (renewal equation), Section 3 (next-generation operator and $R_0$), Section 5, Lemma 5.1, Theorem 5.2, Lemma 5.3, Theorems 5.4 and 5.5 (Lemma 4.1 to Theorem 4.5 in v1).
