# Basic reproduction number and global stability of the age-structured SVEAIR model

**Model.** In a closed population of constant size $N_0$ with birth and death rate $\mu$, let $S$ be susceptible, $V$ vaccinated, $R$ removed, and let $e(t,\theta)$, $a(t,\theta)$, $i(t,\theta)$ be densities of exposed, asymptomatic infectious and symptomatic infectious individuals by age $\theta$ since entering their class. With force of infection $\beta(t) = \int_0^\infty \bigl(\beta_A(\theta) a(t,\theta) + \beta_I(\theta) i(t,\theta)\bigr)d\theta$, vaccination rate $p$, vaccine efficacy $\epsilon \in [0,1)$ against infection, and loss rate $\zeta\epsilon$ of vaccinated individuals,

$$
\begin{aligned}
S' &= \mu N_0 - (p + \beta + \mu) S, \qquad V' = pS - \bigl(\zeta\epsilon + (1-\epsilon)\beta + \mu\bigr)V,\\
(\partial_t + \partial_\theta) e &= -(k + \mu) e, \qquad e(t,0) = \beta(t)\bigl(S + (1-\epsilon)V\bigr),\\
(\partial_t + \partial_\theta) a &= -\bigl(\gamma_A\xi + \chi(1-\xi) + \mu\bigr) a, \qquad a(t,0) = \textstyle\int_0^\infty k q\, e\, d\theta,\\
(\partial_t + \partial_\theta) i &= -(\gamma_I + \mu)\, i, \qquad i(t,0) = \textstyle\int_0^\infty \bigl(k(1-q)\, e + \chi(1-\xi)\, a\bigr) d\theta,
\end{aligned}
$$

where the age-dependent rates are: $k$ leaving latency, $q$ the fraction becoming asymptomatic, $\chi$ symptom onset among asymptomatics (a fraction $\xi$ recovers at rate $\gamma_A$ instead), and $\gamma_I$ recovery of symptomatics.

**Results.**
1. *(Well-posedness.)* For nonnegative $S_0, V_0, R_0$ and nonnegative $e_0, a_0, i_0 \in L^1(\mathbb{R}_+)$, the problem is globally well posed, with $S, V \in C^1$ nonnegative and $e, a, i \in C(\mathbb{R}_+; L^1(\mathbb{R}_+))$ nonnegative.
2. *(Reproduction number.)* Writing $\Pi_g(s) = \exp(-\int_0^s g)$ for survival functions, set

$$
\mathcal{R}_A = \int_0^\infty kq\,\Pi_{k+\mu}\,ds \int_0^\infty \beta_A\,\Pi_{\gamma_A\xi + \chi(1-\xi) + \mu}\,ds,
$$

$$
\mathcal{R}_I = \Bigl(\int_0^\infty k(1-q)\Pi_{k+\mu}\,ds + \int_0^\infty kq\,\Pi_{k+\mu}\,ds \int_0^\infty \chi(1-\xi)\Pi_{\gamma_A\xi + \chi(1-\xi) + \mu}\,ds\Bigr)\int_0^\infty \beta_I\,\Pi_{\gamma_I + \mu}\,ds,
$$

$$
\mathcal{R}_0 = \frac{\mu N_0}{p + \mu}\Bigl(1 + \frac{p(1-\epsilon)}{\zeta\epsilon + \mu}\Bigr)(\mathcal{R}_A + \mathcal{R}_I).
$$

If $\mathcal{R}_0 \le 1$ the only steady state is disease free; if $\mathcal{R}_0 > 1$ there is in addition an endemic steady state, whose force of infection $\beta^* > 0$ solves an explicit quadratic equation.
3. *(Global stability.)* If $\mathcal{R}_0 \le 1$, the disease-free steady state

$$
(S^*, V^*, e^*, a^*, i^*) = \Bigl(\frac{\mu N_0}{p+\mu},\ \frac{p\mu N_0}{(p+\mu)(\zeta\epsilon+\mu)},\ 0, 0, 0\Bigr)
$$

is globally asymptotically stable. If $\mathcal{R}_0 > 1$, the endemic steady state is globally asymptotically stable (for solutions with infection present).

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

$\mathcal{R}_0$ is the product of the effective susceptible pool at the disease-free state, $S^* + (1-\epsilon)V^*$ (written as $\frac{\mu N_0}{p+\mu}(1 + \frac{p(1-\epsilon)}{\zeta\epsilon+\mu})$), and the expected infectiousness of one newly exposed individual. That infectiousness sums the asymptomatic route ($\mathcal{R}_A$: become asymptomatic, then transmit while surviving) and the symptomatic routes ($\mathcal{R}_I$: directly from latency, or via the asymptomatic stage). The steady-state boundary values reduce to a scalar equation in $\beta^*$, whose positive root exists exactly when $\mathcal{R}_0 > 1$. Global stability uses Volterra-type Lyapunov functionals $g(x) = x - 1 - \ln x$ integrated against age-dependent weights, the standard technique for infection-age models.

## Sources

- Vasiliki Bitsouni, Nikolaos Gialelis and Vasilis Tsilidis, "An age-structured SVEAIR epidemiological model", *Mathematical Methods in the Applied Sciences* 47 (2024), 12460–12486, <https://doi.org/10.1002/mma.10165>. Preprint version: arXiv:2311.16049 (2023), scaled age-structured system, Theorem 1, Proposition 1, Corollary 1, definition of $\mathcal{R}_0$, Proposition 2, Corollary 2, Theorems 2–3, <https://doi.org/10.48550/arXiv.2311.16049>.
