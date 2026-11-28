# Permanence and extinction thresholds of the nonautonomous SIQR model

**Model.** Let $S, I, Q, R$ be susceptible, infective, quarantined and recovered individuals, with

$$
\begin{aligned}
S' &= \Lambda(t) - \varphi(t,S,R,Q,I) - d(t)S, \\
I' &= \varphi(t,S,R,Q,I) - [\gamma(t)+\sigma(t)+d(t)+\alpha_1(t)]I, \\
Q' &= \sigma(t)I - [d(t)+\alpha_2(t)+\varepsilon(t)]Q, \\
R' &= \gamma(t)I + \varepsilon(t)Q - d(t)R,
\end{aligned}
$$

where $\Lambda$ is recruitment, $d$ natural mortality, $\gamma$ recovery, $\sigma$ removal to quarantine, $\alpha_1, \alpha_2$ disease deaths and $\varepsilon$ release from quarantine. All rates are continuous, bounded and nonnegative on $[0,\infty)$, and for some $\omega_d, \omega_\Lambda > 0$ the averaged lower bounds $\liminf_{t\to\infty}\int_t^{t+\omega_d}d > 0$ and $\liminf_{t\to\infty}\int_t^{t+\omega_\Lambda}\Lambda > 0$ hold. The incidence $\varphi$ is continuous and nonnegative and satisfies:

- (H1) $S \mapsto \varphi(t,S,R,Q,I)$ is nondecreasing and $\varphi(t,0,R,Q,I) = 0$;
- (H2) for every $\theta > 0$ there is $K_\theta$ with $|\varphi(t,S_1,R,Q,I) - \varphi(t,S_2,R,Q,I)| \le K_\theta|S_1 - S_2|\,I$ on the absorbing region with $S \ge \theta$;
- (H3) there is $N > 0$ with $\inf_{0<\tau<3\delta}\varphi(t,S,0,0,\tau)/\tau \le \varphi(t,S,R,Q,I)/I < N$ whenever $R, Q, I \in (0,\delta)$;
- (H4) $\varphi(t,S,R,Q,I)/I \le \limsup_{\delta\to 0}\varphi(t,S,0,0,\delta)/\delta < \infty$.

**Threshold numbers.** Let $x(t)$ be any solution with $x(0) > 0$ of the total-population equation $x' = \Lambda(t) - d(t)x$, which is the sum of the four equations without disease. Set

$$
b_\delta(t,x) = \frac{\varphi(t,x,0,0,\delta)}{\delta} - (\gamma(t)+\sigma(t)+d(t)+\alpha_1(t)),
$$

$$
r_p(\lambda) = \liminf_{t\to\infty}\int_t^{t+\lambda}\liminf_{\delta\to0}b_\delta(s,x(s))\,ds, \qquad r_e(\lambda) = \limsup_{t\to\infty}\int_t^{t+\lambda}\limsup_{\delta\to0}b_\delta(s,x(s))\,ds,
$$

and $R_p(\lambda) = e^{r_p(\lambda)}$, $R_e(\lambda) = e^{r_e(\lambda)}$. These numbers do not depend on the chosen solution $x(t)$.

The infectives are **permanent** if there are $0 < m_1 < m_2$, independent of the solution, with $m_1 < \liminf I(t) \le \limsup I(t) < m_2$ for every solution with positive initial data, and go **extinct** if $I(t) \to 0$ for all solutions.

**Theorem.**
1. If $R_p(\lambda) > 1$ for some $\lambda > 0$, the infectives are permanent.
2. If $R_e(\lambda) < 1$ for some $\lambda > 0$, the infectives go extinct and every disease-free solution $(x(t), 0, 0, 0)$ is globally attractive.

**Special cases.**
- *Autonomous rates.* With constant parameters and $\varphi = \varphi_0(S,R,Q,I)$, the thresholds become
$R_p^{\mathrm{AUT}} = \liminf_{\delta\to0}\frac{\varphi_0(\Lambda/d,0,0,\delta)}{\delta(\gamma+\sigma+d+\alpha_1)}$ and $R_e^{\mathrm{AUT}} = \limsup_{\delta\to0}\frac{\varphi_0(\Lambda/d,0,0,\delta)}{\delta(\gamma+\sigma+d+\alpha_1)}$: permanence if $R_p^{\mathrm{AUT}} > 1$, extinction if $R_e^{\mathrm{AUT}} < 1$. For mass-action incidence $\beta SI$ both equal the quarantine reproduction number $\beta\Lambda/[d(\gamma+\sigma+d+\alpha_1)]$; for standard incidence $\beta SI/(S+I+Q+R)$ and quarantine-adjusted incidence $\beta SI/(S+I+R)$ both equal $\beta/(\gamma+\sigma+d+\alpha_1)$. For $\varphi_0 = S\,I^p/(1+aI^q)$ with $p<1$ the infectives are always permanent.
- *Asymptotically autonomous rates.* Suppose the rates converge to constants, $\varphi(t,S,R,Q,I) \to \varphi_0(S,R,Q,I)$ for each state with $\varphi_0$ continuous, the right-hand side of the system converges to that of the limit system uniformly on every compact subset of $[0,\infty)^4$, and both right-hand sides are locally Lipschitz in $(S,R,Q,I)$. Then the autonomous thresholds of the limit system decide permanence and extinction.
- *Periodic rates.* If $\Lambda$ and $d$ are constant and the other rates and $\varphi$ are $T$-periodic in $t$, write $\bar f = \frac1T\int_0^Tf$. Then permanence holds if $\frac1T\int_0^T\liminf_{\delta\to0}\frac{\varphi(s,\Lambda/d,0,0,\delta)}{\delta}\,ds > \bar\gamma + \bar\sigma + d + \bar\alpha_1$, and extinction holds if the same inequality with $\limsup$ is reversed.

## Expansion

The total-population equation has a globally uniformly attracting bounded solution, uniformly bounded away from zero, and perturbing it by a bounded forcing moves it by at most a constant times the forcing. When $I$ is small, $Q$ and $R$ are small too, so $S$ stays close to $x(t)$ and, by (H2)–(H4), $I'/I$ is within a small error of $b_\delta(t, x(t))$. For extinction, $\int_t^{t+\lambda}I'/I < r_e(\lambda) + \text{error} < 0$ over consecutive windows of length $\lambda$, so $I$ decays geometrically. For permanence, a positive average growth rate over every window pushes $I$ away from zero, and comparing the windows gives a lower bound independent of the solution. Independence of $x(t)$ comes from the Lipschitz estimate (H2) together with the fact that all solutions of the total-population equation converge to one another exponentially.

## Sources

- César M. Silva, "A nonautonomous epidemic model with general incidence and isolation", arXiv:1205.5740 (2012), Section 2 (model and Propositions 1–2), Section 3 (Lemma 1 and Theorem 1), Theorem 2 (autonomous case), Theorem 4 (asymptotically autonomous case), Theorem 5 (periodic case), Theorems 6–7 (mass-action, standard and quarantine-adjusted incidence), <https://doi.org/10.48550/arXiv.1205.5740>. Published version: Mathematical Methods in the Applied Sciences 37(13) (2014), 1974–1991, <https://doi.org/10.1002/mma.2950>; locators above refer to the arXiv version.
