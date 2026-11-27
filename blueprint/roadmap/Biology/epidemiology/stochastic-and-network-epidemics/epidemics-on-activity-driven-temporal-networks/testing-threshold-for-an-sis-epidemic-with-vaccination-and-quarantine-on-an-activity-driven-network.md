# Testing threshold for an SIS epidemic with vaccination and quarantine on an activity-driven network

**Model.** Each of $n$ individuals is susceptible (S), infectious with mild symptoms (I) or quarantined (Q). Encounters follow an activity-driven temporal network: every individual activates at unit rate and contacts a uniformly random other individual. An encounter with an I individual happens at close proximity with probability $1 - \sigma$ (a mildly symptomatic person keeps distance with probability $\sigma$), and transmits with per-contact probability $\lambda$ reduced by non-pharmaceutical interventions of effectiveness $\eta$ and by vaccination of a fraction $v$ of the population with effectiveness $\gamma_t$ against transmission: the factor is $(1-\eta)(1-\gamma_t v)\lambda$. A new infection is severe and goes straight to Q with probability $p_q(1 - \gamma_q v)$ ($\gamma_q$ the effectiveness against severe illness), otherwise to I. Infectious individuals are detected by testing at rate $c_t$ and quarantined, and I and Q individuals recover to S at rate $\beta$. In the mean-field equations for individual probabilities $(s_j, i_j, q_j)$, write $\Theta = 2(1-\eta)(1-\sigma)\lambda(1-\gamma_t v)$ and $\pi = 1 - p_q(1 - \gamma_q v)$.

**Theorem.** In the limit $n \to \infty$ the epidemic threshold for the testing rate is

$$\bar c_t = \Theta\,\pi - \beta.$$

1. If $c_t \ge \bar c_t$, the population-averaged state $(y_s, y_i, y_q)$ converges to the disease-free equilibrium $(1, 0, 0)$, which is locally asymptotically stable when $c_t > \bar c_t$.
2. If $c_t < \bar c_t$ and $y_i(0) > 0$, it converges to the endemic equilibrium

$$y_s^* = \frac{\beta + c_t}{\Theta\,\pi}, \qquad y_i^* = \frac{\beta\,\pi}{\beta + c_t} - \frac{\beta}{\Theta}, \qquad y_q^* = \Big(1 - \frac{\beta\,\pi}{\beta + c_t}\Big)\Big(1 - \frac{\beta + c_t}{\Theta\,\pi}\Big).$$

The simplex $\{s_j, i_j, q_j \ge 0,\ s_j + i_j + q_j = 1\}$ is positively invariant for each individual.

## Proof sketch

Averaging over individuals, the infectious fraction obeys $\dot y_i = \Theta\,\pi\,y_s y_i - (\beta + c_t)y_i$ up to $O(1/n)$ terms, since each activation (own or partner's, hence the factor $2$) creates a close-proximity contact with an I individual with probability proportional to $(1-\sigma)y_i$. Linearizing at $y_s = 1$ gives growth rate $\Theta\pi - \beta - c_t$, which is the threshold. The equivalent reproduction number is $\Theta\pi/(\beta + c_t)$: vaccination, NPIs and responsible behaviour ($\sigma$) lower $\Theta$, quarantine of severe cases lowers $\pi$, and testing raises the removal rate from the transmitting class. Above threshold the endemic state follows by solving the stationary equations with $y_s + y_i + y_q = 1$; convergence holds from every initial condition with $y_i(0) > 0$. The model is used to show how waning NPIs after partial vaccination can produce resurgent outbreaks.

## Sources

- Kathinka Frieswijk, Lorenzo Zino and Ming Cao, "Modelling the Effect of Vaccination and Human Behaviour on the Spread of Epidemic Diseases on Temporal Networks", in *2022 European Control Conference (ECC)*, IEEE, 2022, 2291–2296, <https://doi.org/10.23919/ecc55457.2022.9838287>. Preprint version: arXiv:2111.05590 (2021), model and control measures (Section 3), mean-field equations (Section 4), Lemma 1 and Theorems 1 and 2 (Section 5), <https://doi.org/10.48550/arXiv.2111.05590>.
