# Basic reproduction number of a delayed SEIR model with health-care-capacity-dependent rates

**Model.** A population with births at constant rate $b > 0$ and natural death rate $d > 0$ is split into susceptible $S$, exposed $E$, infectious $I$ and recovered $R$ individuals. Transmission is mass action with rate $\beta > 0$, the latent period is a fixed delay $\tau \ge 0$ with survival factor $e^{-d\tau}$, $\gamma > 0$ is the progression factor into $I$, and $\delta \ge 0$ moves non-infectious exposed individuals to $R$. A constant $c \in [0, 1]$ measures how much of the health-care capacity is available to infectious individuals: the recovery rate is $\alpha_1 + \alpha_2 c$ and the disease-induced death rate is $\mu_1 + \mu_2 (1 - c)$, with $\alpha_1, \alpha_2, \mu_1, \mu_2 \ge 0$, so $c = 1$ gives the maximal recovery and minimal death rate. Write

$$K(c) = \mu_1 + \mu_2 (1 - c) + \alpha_1 + \alpha_2 c + d .$$

Since $E$ and $R$ do not feed back into the other equations, the dynamics reduce to the delay system

$$S'(t) = b - \beta S(t) I(t) - d S(t), \qquad I'(t) = \gamma \beta e^{-d\tau} S(t - \tau) I(t - \tau) - K(c)\, I(t),$$

and the set $\Gamma = \{S, E, I, R \ge 0,\ S + E + I + R \le b/d\}$ is positively invariant and attracting.

**Proposition.** Let

$$R_0 = \frac{b \beta \gamma e^{-d\tau}}{d\, K(c)} .$$

1. The disease-free equilibrium $P_0 = (b/d, 0)$ always exists; it is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.
2. A positive (endemic) equilibrium exists if and only if $R_0 > 1$; it is unique and equals

    $$P^* = (S^*, I^*) = \Big(\frac{b}{d R_0},\ \frac{d}{\beta}(R_0 - 1)\Big).$$

3. $R_0$ is a decreasing function of the capacity level $c$ exactly when $\alpha_2 > \mu_2$, that is, when access to care raises the recovery rate by more than it lowers the death rate.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

With infected variable $I$ only, the new-infection and transfer terms at $P_0$ are the scalars $F = \gamma\beta e^{-d\tau} b/d$ and $V = K(c)$, so $R_0 = F V^{-1}$. Linearizing the delay system at $P_0$ gives the eigenvalue $-d$ and the roots of $\lambda + K = K R_0 e^{-\lambda\tau}$. If $R_0 < 1$ and $\operatorname{Re}\lambda \ge 0$, then $|\lambda + K| \ge K > K R_0 \ge |K R_0 e^{-\lambda\tau}|$, a contradiction, so all roots lie in the left half-plane; if $R_0 > 1$, the real function $h(\lambda) = \lambda + K - K R_0 e^{-\lambda \tau}$ satisfies $h(0) < 0$ and $h(\lambda) \to \infty$, so a positive root exists. (The source computes the characteristic equation with the delay suppressed; the threshold is the same.) At an endemic equilibrium the second equation forces $S^* = K e^{d\tau}/(\gamma\beta) = b/(d R_0)$, and the first gives $I^* = (b - d S^*)/(\beta S^*) = d(R_0 - 1)/\beta$, positive exactly when $R_0 > 1$. Item 3 follows from $K(c) = \mu_1 + \mu_2 + \alpha_1 + d + (\alpha_2 - \mu_2) c$.

## Sources

- S. Çakan, "Dynamic analysis of a mathematical model with health care capacity for COVID-19 pandemic", *Chaos, Solitons & Fractals* 139 (2020) 110033, Sections 2.1–2.4: model (1)–(3), reduced system (6), $R_0$ in Eq. (8), endemic equilibrium, Theorems 1–2; item 3 and the delay-aware root argument are derived here. <https://doi.org/10.1016/j.chaos.2020.110033> (PMC7305938).
