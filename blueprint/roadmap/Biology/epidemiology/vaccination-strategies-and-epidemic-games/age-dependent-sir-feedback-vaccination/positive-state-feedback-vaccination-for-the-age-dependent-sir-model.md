# Positive state-feedback vaccination law for the age-dependent SIR model

In the age-structured SIR model on ages $a \in [0, L]$ (same units for age and time),

$$
(\partial_t + \partial_a) S = -\big(\Theta(t,a) + \mu(a)\big)S - \beta(a)\,S \int_0^L I(t,b)\,db, \qquad (\partial_t + \partial_a) I = -\big(\mu(a) + \gamma(a)\big) I + \beta(a)\,S \int_0^L I(t,b)\,db,
$$

with recovered class $(\partial_t + \partial_a) R = \Theta S + \gamma I - \mu R$, boundary conditions $S(t,0) = B$ (constant birth rate), $I(t,0) = R(t,0) = 0$, age-dependent mortality $\mu$, recovery rate $\gamma$, transmission rate $\beta$ and vaccination rate $\Theta(t,a) \ge 0$ as the control, consider the nonlinear state-feedback law

$$
\Theta(t,a) = \tilde\alpha_2(a) + \int_0^L \beta(a) S(t,a)\,da - 2\mu(a) - \gamma(a) - \beta(a)\int_0^L I(t,b)\,db - \frac{\int_0^L (\mu(a)+\gamma(a)) I(t,a)\,da}{\int_0^L I(t,b)\,db} + \frac{I(t,a)\,\big(\tilde\alpha_1(a) + (\mu(a)+\gamma(a))(\mu(a)+\gamma(a)-\tilde\alpha_2(a))\big)}{\beta(a)\,S(t,a)\int_0^L I(t,b)\,db},
$$

obtained as the continuous-age limit of a feedback for the age-discretized model, with tuning functions $\tilde\alpha_1, \tilde\alpha_2$.

**Theorem.** Let $\nu = \sup_a \mu(a)$, $\Gamma = \sup_a \gamma(a)$ and $N$ the total population. With

$$
\tilde\alpha_2(a) = 3\nu + 2\Gamma + \beta(a)N, \qquad \tilde\alpha_1(a) = -\big(\mu(a) + \gamma(a)\big)\big(\mu(a) + \gamma(a) - \tilde\alpha_2(a)\big),
$$

the closed-loop system is locally exponentially stable and the vaccination law $\Theta$ is non-negative. More generally, whenever the tuning constants satisfy the paper's explicit inequalities, the feedback drives the infected population to zero exponentially: $\|I(t,\cdot)\|_{L^1} \to 0$ as $t \to \infty$. For a time-independent vaccination rate $\Theta^\star(a)$, with $c(b) = B\exp(-\int_0^b \mu)$ the limiting age profile and $\Gamma(b) = \exp(-\int_0^b \gamma)$, define

$$
R(0) = \int_0^L c(b)\,\Gamma(b) \int_0^b \frac{\beta(\sigma)}{\Gamma(\sigma)} \exp\Big(-\int_0^\sigma \Theta^\star(\eta)\,d\eta\Big)\,d\sigma\,db ;
$$

then the disease-free equilibrium is locally exponentially stable if $R(0) \le 1$ and unstable if $R(0) > 1$, in which case the endemic equilibrium is locally exponentially stable.

## Expansion

With the choice of $\tilde\alpha_1$ in the theorem the last term of $\Theta$ vanishes. The feedback is designed so that the total infected population $\int I$ obeys closed-loop linear dynamics with tunable decay, in the spirit of input–output linearization; positivity of $\Theta$ is needed for the law to be a vaccination rate and is secured by choosing $\tilde\alpha_2$ larger than the worst-case mortality, recovery and transmission terms. Well-posedness of the closed loop on $L^1$ follows from semigroup generation for boundary control systems and bounded perturbation, and local stability from the linearization principle. In practice, because the law divides by $\int I \to 0$, the paper switches to zero vaccination once prevalence is small.

## Sources

- Candy Sonveaux and Joseph J. Winkin, *State feedback control law design for an age-dependent SIR model*, arXiv:2205.08140, Corollary 1 (Section 3) and the stability, positivity and semigroup results of Section 5 ("Closed-loop stabilization of PIDE model"). <https://doi.org/10.48550/arXiv.2205.08140> Published version: Automatica 158 (2023) 111297, <https://doi.org/10.1016/j.automatica.2023.111297>.
