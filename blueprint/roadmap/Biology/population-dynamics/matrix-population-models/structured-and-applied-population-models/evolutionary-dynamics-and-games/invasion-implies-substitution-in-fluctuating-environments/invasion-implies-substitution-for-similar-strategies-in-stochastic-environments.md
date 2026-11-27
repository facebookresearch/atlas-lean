# Invasion implies substitution for similar strategies in stochastic environments

**Model.** Subpopulations with strategies $x_1, \dots, x_k$ grow as $\dot n_{i,t} = f(x_i, e_t, \theta_t)\,n_{i,t}$ in a feedback environment $e_t = (e_{1,t}, e_{2,t})$ with $\dot e_{1,t} = G_1(e_t,\theta_t) + \sum_j H_1(x_j, e_t, \theta_t)n_{j,t}$ and $e_{2,t} = G_2(e_t,\theta_t) + \sum_j H_2(x_j,e_t,\theta_t)n_{j,t}$, driven by an external diffusion $\dot\theta_t = A(\theta_t) + B(\theta_t)\dot W_t$ that is ergodic with invariant law $\nu$. A *resident* is a population with an invariant probability measure $\mu$ supported off the extinction set, with zero long-run per-capita growth and stochastic persistence. The **invasion fitness** of a rare mutant $y$ is its almost-sure long-run growth rate

$$S_{x}(y) = \lim_{t\to\infty}\frac{1}{t}\int_0^t f(y, e_s, \theta_s)\,ds = \int f(y, e, \theta)\,\mu(de\,d\theta),$$

and $S_x(x) = 0$.

**Similar strategies.** Let $x_i = x + \epsilon\xi_i$ ($i = 1,2$, $\xi_1 \ne \xi_2$) and let $P_t^\epsilon = n_{2,t}/(n_{1,t} + n_{2,t})$. On the slow time $t_1 = \epsilon t$, averaging over the fast resident–environment process gives

$$\dot{\bar P}_{t_1} = \bar P_{t_1}(1 - \bar P_{t_1})\,\partial_y S_x(y)|_{y=x}\,(\xi_2 - \xi_1),$$

and $S_{x_1}(x_2) = -S_{x_2}(x_1) = \epsilon\,\partial_y S_x(y)|_{y=x}(\xi_2 - \xi_1) + O(\epsilon^2)$.

**Theorem (invasion implies substitution).** Assume $\int|f(y,e,\theta)|^2\mu(de\,d\theta) < \infty$ for $y$ near $x$ and $\partial_y S_x(y)|_{y=x}(\xi_2 - \xi_1) \ne 0$. For every $\delta \in (0,1)$ there is $T_\delta$ such that, for all initial $p \in (0,1)$ and $\mu$-a.e. initial state,

$$P\Big\{\lim_{\epsilon\to 0}\sup_{t_1 \ge T_\delta}|P^\epsilon_{t_1} - p^*| \le \delta\Big\} = 1,$$

with $p^* = 1$ if $S_{x_1}(x_2) > 0 > S_{x_2}(x_1)$ and $p^* = 0$ if $S_{x_1}(x_2) < 0 < S_{x_2}(x_1)$. So away from evolutionarily singular strategies (and, in several dimensions, for deviations not orthogonal to the selection gradient) a successful invader of a similar resident replaces it, even in a fluctuating environment.

## Depends on

- [Fitness Gradient](../../../../classification-of-adaptive-dynamics-singular-str/fitness-gradient.md)

## Expansion

Writing the system in total size $N^\epsilon$ and frequency $P^\epsilon$, the frequency moves only at order $\epsilon$, with speed $P(1-P)\,\partial_x f(x, e_t, \theta_t)^\top(\xi_2 - \xi_1)$. Birkhoff's ergodic theorem turns the time average of $\partial_x f$ along the fast resident process into the selection gradient $\int\partial_x f\,d\mu = \partial_y S_x(y)|_{y=x}$. The stochastic averaging principle (Khasminskii; Freidlin–Wentzell) gives closeness to the averaged logistic equation on finite intervals, and stability of its boundary equilibria extends this to infinite horizons. This is the stochastic counterpart of Geritz's deterministic invasion-implies-fixation result.

## Sources

- Y. Cai, S. A. H. Geritz, "Resident-invader dynamics of similar strategies in fluctuating environments", Journal of Mathematical Biology 81 (2020) 907–959, Sect. 2, equations (2.1)–(2.11), Definition 1, Lemma 1 and Theorem 1, <https://doi.org/10.1007/s00285-020-01532-8>, PMCID: PMC7560957.
