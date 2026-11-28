# Evolutionarily stable vaccination responses to a premature vaccine

**Model.** A growing population with SIS-type infection is described by the infected fraction $\theta$, the vaccinated fraction $\psi$, the susceptible fraction $\phi = 1 - \theta - \psi$ and a size variable $\eta$, with infection rate $\lambda$, recovery $r$, births $b$, deaths $d$ and excess deaths $d_e$. Agents contact the vaccination facility at rate $\nu$ and vaccinate with probability $q(\theta,\psi) = \min\{\tilde q(\theta,\psi),1\}$, where the response $\tilde q$ is a *policy* $\pi(\hat\beta)$ from a family $\Pi$ (e.g. responses increasing with the vaccinated fraction, $\tilde q = \hat\beta\psi$, reflecting reported side effects and growing confidence, or with the infected fraction). The stochastic system is approximated, via stochastic approximation, by the ODE

$$\dot\theta = \frac{\theta}{\eta\varrho}\big[\phi\lambda - r - d_e - (b - d_e\theta)\big], \qquad \dot\psi = \frac{1}{\eta\varrho}\big[q(\theta,\psi)\phi\nu - (b - d_e\theta)\psi\big],$$

with $\varrho = b + d + d_e\theta + \lambda\theta\phi + \nu\phi + r\theta$. Set $\rho = \lambda/(r + b + d_e)$ and $\mu = b/\nu$.

**Utility and stability.** At the limit state $(\hat\theta,\hat\psi)$ of policy $\pi(\hat\beta)$, an agent vaccinating with probability $q$ pays $u(q;\pi) = q\,h(\hat\theta,\hat\psi) + p_I(\hat\theta)(c_{I_1} + c_{I_2}d_e\hat\theta)$, where

$$h(\hat\theta,\hat\psi) = c_{v_1} + \min\Big\{\bar c_{v_2}, \frac{c_{v_2}}{\hat\psi}\Big\} - p_I(\hat\theta)\big(c_{I_1} + c_{I_2}d_e\hat\theta\big)$$

balances vaccination cost and perceived side-effect risk (lower when many are already vaccinated) against infection risk $p_I$. A policy is an **ESS-AS** if the equilibrium vaccination probability $q^*$ is the unique best response and remains so against every small $\varepsilon$-fraction of mutants. Let $h_m = h(1 - 1/\rho, 0)$, the vaccination incentive in the unvaccinated endemic state.

**Theorem.** Assume there are no excess deaths, $d_e = 0$ (the case the source analyses; then $\rho = \lambda/(r+b)$ and $h_m = c_{v_1} + \bar c_{v_2} - p_I(1 - 1/\rho)\,c_{I_1}$). For $d_e > 0$ the zero of the $\theta$-equation with $q = 1$ is $\phi = (r + b + d_e - d_e\theta)/\lambda \ne 1/\rho$, and the source leaves that case open.

1. If $\rho < 1$, or if $\rho > 1$ and $h_m > 0$, the non-vaccinating policy $\pi(0)$ is an ESS-AS within any family $\Pi$.
2. If $\rho > 1$ and $h_m < 0$, an ESS-AS exists in $\Pi$ if and only if (i) some $\beta^* > 0$ makes $q = 1$ but $\tilde q \ne 1$ at the attractor of $\pi(\beta^*)$, and (ii) that attractor is

$$(\theta_E,\psi_E) = \Big(1 - \frac1\rho - \frac{1}{\mu\rho},\ \frac{1}{\mu\rho}\Big) \ \text{ with } \mu\rho > \mu + 1, \quad\text{and}\quad h(\theta_E,\psi_E) < 0.$$

Hence at any vaccinating evolutionarily stable outcome everyone who reaches the facility vaccinates, yet the disease settles at the endemic level $\theta_E > 0$: limiting states that eradicate the disease exist for some responses, but none is stable against mutations.

## Expansion

The utility is linear in $q$ with slope $h$, so the best response is $q = 0$ when $h > 0$ and $q = 1$ when $h < 0$; an ESS needs the induced equilibrium to reproduce that sign. If $\rho < 1$ the disease dies out by itself and nobody needs to vaccinate. Otherwise a vaccinating ESS must induce full vaccination of contacting agents, and setting $q = 1$ in the ODE gives the unique interior zero $\phi = 1/\rho$, $\psi = \phi\nu/b$, i.e. $(\theta_E,\psi_E)$, which is positive exactly when $\mu\rho > \mu + 1$. Robustness to mutants follows from continuity of the attractor in the mutant fraction when $\tilde q \ne 1$ at the attractor (so the response is not exactly at the cap).

## Sources

- Vartika Singh, Khushboo Agarwal, Shubham, Veeraruna Kavitha, "Evolutionary vaccination games with premature vaccines to combat ongoing deadly pandemic", arXiv (2021). Problem description (ESS-AS and utility definitions), ODE approximation theorem and the ODE system, the limit-proportion theorems for FC, FR and VFC agents, the lemma on $\pi(0)$ and the vaccinating-ESS theorem; appendices on stochastic approximation and attractors. <https://doi.org/10.48550/arXiv.2109.06008>. Published version: Performance Evaluation Methodologies and Tools (VALUETOOLS 2021), Lecture Notes of the Institute for Computer Sciences, Social Informatics and Telecommunications Engineering (2021), 185–206, <https://doi.org/10.1007/978-3-030-92511-6_12>; locators above refer to the arXiv version.
