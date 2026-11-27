# Dynamic programming and verification for age-structured SIR with capital accumulation

**Model.** Ages lie in $[0, \bar a]$. Susceptible, infected and recovered densities $s, i, r$ satisfy the McKendrick-type system

$$(\partial_t + \partial_a)s = -\lambda^{\theta,\eta} s - \mu_S(a)s, \qquad (\partial_t + \partial_a)i = \lambda^{\theta,\eta} s - \big(\mu_I(a, \Xi(t)) + \gamma(a)\big)i, \qquad (\partial_t + \partial_a)r = \gamma(a)i - \mu_R(a)r,$$

with births $s(0,t) = \int_0^{\bar a}\beta(a)\, n(a,t)\, da$ ($n = s + i + r$), $i(0,t) = r(0,t) = 0$, and the controlled force of infection

$$\lambda^{\theta,\eta}(a,t) = \frac{\theta(a,t)}{N(t)}\int_0^{\bar a} m(a,\tau)\, \theta(\tau,t)\, \eta(\tau,t)\, i(\tau,t)\, d\tau,$$

where $\theta \in [0,1]$ is a mobility (lockdown) factor, $\eta \in [0,1]$ an infectiousness factor bought by testing, $m$ the contact kernel, and the infected mortality $\mu_I$ depends on an aggregate infection load $\Xi$ (hospital congestion). Capital follows

$$\dot K = F(K, L) - \int_0^{\bar a} c\, n\, da - \delta K - D\Big(\int_0^{\bar a}\eta\, i\, e\, da\Big), \qquad L = \int_0^{\bar a}(s + r)\,\alpha(a)\,\varphi(\theta)\, da,$$

and the planner maximizes, for example, the welfare $\int_0^\infty\int_0^{\bar a} e^{-\rho t}\, n^\nu u(c, \theta)\, da\, dt$ over consumption $c$, $\theta$ and $\eta$.

**Hypotheses.** $\mu_S, \mu_R > 0$ are locally integrable with $\int_0^{\bar a}\mu_S = \int_0^{\bar a}\mu_R = \infty$ (nobody survives past $\bar a$); $\mu_I(a,\kappa)$ is measurable, Lipschitz and increasing in $\kappa$ uniformly in $a$, with $\int_0^{\bar a}\mu_I(a,\kappa)\, da = \infty$ for every $\kappa$; $F(\cdot, L)$ is Lipschitz for every $L \ge 0$, with Lipschitz constants bounded uniformly in $L$; $\varphi : [0,1] \to [0,1]$ is increasing with $\varphi(1) = 1$; the age profiles $\alpha, \beta, \gamma, e$ (and the source's further profile $\xi$) are non-negative and in $L^2(0,\bar a)$; $D$ is positive and concave; $\delta > 0$ and $\nu \in [0,1]$; and $u : \mathbb{R} \times [0,1] \to \mathbb{R}$ is positive, continuous and increasing in both variables (the source's Hypothesis 3.1(i)–(viii)).

**Theorem.**

1. *(Well-posedness.)* In a weighted Hilbert space $H$ of age profiles, the age-transport-with-mortality operator $\tilde A$ generates a strongly continuous semigroup on $H \times \mathbb{R}$ that leaves the positive cone invariant, the nonlinear infection and capital terms are Lipschitz, and the controlled state equation has a unique mild solution, which coincides with the solution of the PDE system.
2. *(Verification.)* Let $v$ be a classical solution of the associated Hamilton–Jacobi–Bellman equation $\rho v = \sup_{z}\mathbb{H}_{CV}(h, K, D_h v, D_K v; z)$ on the interior of the admissible state set, with $D_h v$ in the domain of $\tilde A^*$, such that $e^{-\rho T} v(h(T), K(T)) \to 0$ along every admissible trajectory. Then $v$ bounds the value function from above, and an admissible strategy whose controls attain the supremum in the Hamiltonian along its own trajectory is optimal, with value $v$. If the argmax admits a measurable selection $G$ and the closed-loop equation with $z = G(h, K)$ has an admissible solution, this feedback is optimal; conversely an optimal control satisfies the Hamiltonian maximum condition whenever the value function is a classical solution with the transversality property.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Integrating along characteristics turns the infinite-mortality conditions into the boundary behavior that makes the age-transport operator dissipative in the chosen weighted norm; the weight is put only on the susceptible component because $\mu_I$ is state-dependent, which enlarges the space but keeps the nonlinearity Lipschitz. For verification, write $J$ along an admissible trajectory and apply the chain rule to $e^{-\rho t}v(h(t), K(t))$ (justified because $D_h v \in D(\tilde A^*)$): the HJB equation gives $\frac{d}{dt}\big(e^{-\rho t}v\big) \le -e^{-\rho t}\,(\text{running reward})$ with equality exactly when the control maximizes the current-value Hamiltonian; integrating to $T$ and using transversality yields both claims. The result reduces finding optimal age-targeted lockdown and testing policies to solving, even numerically, the HJB equation.

## Sources

- Giorgio Fabbri, Fausto Gozzi, Giovanni Zanco, "Verification results for age-structured models of economic–epidemics dynamics", Journal of Mathematical Economics 93 (2021), 102455, <https://doi.org/10.1016/j.jmateco.2020.102455>. Published version of arXiv:2008.07335, cited next; locators there refer to the arXiv version.
- Giorgio Fabbri, Fausto Gozzi, Giovanni Zanco, "Verification Results for Age-Structured Models of Economic-Epidemics Dynamics", arXiv (2020). Section 2 (model), Hypothesis 3.1, Proposition 3.4, Definition 4.1, Theorem 4.2, Theorem 5.2, Corollaries 5.3 and 5.4. <https://doi.org/10.48550/arXiv.2008.07335>
