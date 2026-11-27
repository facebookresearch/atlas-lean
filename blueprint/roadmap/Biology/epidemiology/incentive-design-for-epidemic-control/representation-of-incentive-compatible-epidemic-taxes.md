# Representation of incentive-compatible epidemic taxes

In the [stochastic SIS–SIR model with testing and contact control](stochastic-sis-sir-model-with-testing-and-contact-control.md), the government announces a testing policy $\alpha$ and a tax $\chi$, an $\mathcal F_T$-measurable random variable of the path of $(S, I)$. The population chooses $\beta \in \mathcal B$ to maximize

$$J^A_0(\alpha, \chi, \beta) = \mathbb E^{\mathbb P^{\alpha,\beta}}\Bigl[\int_0^T u(t, \beta_t, I_t)\,dt + U(-\chi)\Bigr], \tag{4.6}$$

where $u$ is a continuous running utility of contacts and $U$ is an increasing utility of the (negative) tax, with $\mathbb E^{\mathbb P^\alpha}[|U(-\chi)|^p] < \infty$ for some $p > 1$. Assume there is a unique Borel map $b^\star(t, s, i, z, a) \in \arg\max_{b \in B}\{u(t, b, i) - b\sqrt{a}\,s\,i\,z\}$ (Assumption 4.5).

**Theorem 4.7.** For every admissible $(\alpha, \chi)$ there exist a unique $\mathcal F^{+}_0$-measurable $Y_0$ and a unique process $Z$ in $\mathbb H^p(\mathbb P^\alpha)$ such that, $\mathbb P^\alpha$-a.s.,

$$U(-\chi) = Y_0 - \int_0^T\Bigl(Z_t(\mu + \nu + \gamma + \rho)I_t + u(t, \beta^\star_t, I_t) - \beta^\star_t\sqrt{\alpha_t}\, S_t I_t Z_t\Bigr)dt - \int_0^T Z_t\,dI_t, \tag{4.12}$$

with $\beta^\star_t = b^\star(t, S_t, I_t, Z_t, \alpha_t)$. Moreover $\beta^\star$ is the unique optimal contact policy and the population's value is $V^A_0(\alpha, \chi) = \mathbb E^{\mathbb P^\alpha}[Y_0]$.

**Consequences.** By Lemma 4.8, $Y_0$ may be replaced by the constant $\mathbb E^{\mathbb P^\alpha}[Y_0]$ without changing the value or the optimal response. So every incentive-compatible tax is parametrized by a constant $y_0 \ge \underline v$ (the participation level) and a process $Z$, and it is indexed on the path of $I$ alone (equivalently on $S$ alone, since both are driven by the same Brownian motion with opposite signs). By Lemma 4.9 the government's problem $\sup \mathbb E[\chi - \int_0^T (c(I_t) + k(t, \alpha_t, S_t, I_t))\,dt]$ becomes a standard stochastic control problem over $(\alpha, Z)$ with state $(S, I, Y)$, solved through a Hamilton–Jacobi–Bellman equation in the variables $(t, s, i, y)$ on the domain $\{(t, s, i, y) : t \in [0, T),\ 0 < s + i < F(t, s_0, i_0),\ y \in \mathbb R\}$. Only the epidemiological coordinates are bounded; the continuation-utility coordinate $y$ ranges over all of $\mathbb R$, and truncating it is a separate numerical step.

## Depends on

- [Stochastic SIS–SIR model with testing and controlled contact rate](stochastic-sis-sir-model-with-testing-and-contact-control.md)

## Proof depends on

- [Girsanov's theorem for bounded progressive drift](../../../Probability/stochastic-calculus/it-s-formula/girsanov-change-of-measure-for-bounded-drift.md)

## Expansion

Solve the backward SDE

$$Y_t = U(-\chi) + \int_t^T \sup_{b \in B}\{u(r, b, I_r) - Z_r b\sqrt{\alpha_r}\, S_r I_r\}\,dr - \int_t^T Z_r\,\sigma\alpha_r S_r I_r\,dW_r,$$

which is well posed because $B$ is compact, $u$ is continuous and $S, I$ are bounded. Writing $\sigma\alpha S I\,dW = -(dI + (\mu + \nu + \gamma + \rho)I\,dt)$ under $\mathbb P^\alpha$ and evaluating at $t = 0$ gives (4.12). Substituting (4.12) into $J^A_0$ for an arbitrary $\beta$ and using that $\int Z\,dI$ has drift $\beta\sqrt{\alpha}\,SIZ - (\mu + \nu + \gamma + \rho)IZ$ under $\mathbb P^{\alpha,\beta}$ gives

$$J^A_0 = \mathbb E[Y_0] + \mathbb E^{\mathbb P^{\alpha,\beta}}\Bigl[\int_0^T \bigl(u(t, \beta_t, I_t) - \beta_t\sqrt{\alpha_t}\, S_t I_t Z_t\bigr) - \bigl(u(t, \beta^\star_t, I_t) - \beta^\star_t\sqrt{\alpha_t}\, S_t I_t Z_t\bigr)\,dt\Bigr] \le \mathbb E[Y_0],$$

with equality iff $\beta = \beta^\star$ by uniqueness of the maximizer. Here $Z$ is the marginal sensitivity of the population's continuation utility to new infections. A larger $Z$ makes contacts costlier and lowers $\beta^\star$.

## Sources

- E. Hubert, T. Mastrolia, D. Possamaï and X. Warin, "Incentives, lockdown, and testing: from Thucydides' analysis to the COVID-19 pandemic", Journal of Mathematical Biology 84 (2022), 37, Section 2 (Equations (2.14)–(2.16)) and Section 4 (Equations (4.6)–(4.14), Assumption 4.5, Theorem 4.7, Lemmas 4.8–4.9, and the domain of the HJB equation (4.19)), <https://doi.org/10.1007/s00285-022-01736-0>, PMCID PMC8995008.
