# Extinction and permanence in a vector-borne SEIRS model with random delays

**Model.** Consider a dimensionless model of a vector-borne infection in which only the host compartments $S, E, I, R$ are tracked and the infectious vector population at time $t$ is taken proportional to the infectious host population one vector incubation period earlier. Three delays are random: the incubation period $T_1$ in the vector with density $f_{T_1}$ on $[t_0, h_1]$, the incubation period $T_2$ in the host with density $f_{T_2}$ on $[t_0, h_2]$, and the immunity period $T_3$ with density $f_{T_3}$ on $[t_0, \infty)$. Host births occur at constant rate $B$, natural and disease deaths at rates $\mu$ and $d$, recovery at rate $\alpha$, vector deaths at rate $\mu_v$, and $\beta > 0$ is the effective contact rate. After normalisation $B/\mu = 1$. The decoupled $S$–$I$ system is

$$
\frac{dS}{dt} = B - \beta S(t)\int_{t_0}^{h_1} f_{T_1}(s)e^{-\mu_v s}G(I(t-s))\,ds - \mu S(t) + \alpha\int_{t_0}^{\infty} f_{T_3}(r)e^{-\mu r}I(t-r)\,dr,
$$

$$
\frac{dI}{dt} = \beta\int_{t_0}^{h_2}\int_{t_0}^{h_1} f_{T_2}(u)f_{T_1}(s)e^{-\mu_v s-\mu u}S(t-u)G(I(t-s-u))\,ds\,du - (\mu+d+\alpha)I(t),
$$

with continuous positive initial histories in a fading-memory space. The incidence function $G$ satisfies $G(0) = 0$; $G$ is strictly monotone, $C^2$ and strictly concave on $[0,\infty)$; $\lim_{I\to\infty}G(I) < \infty$; $G(I) \le I$; and $\left(\frac{G(x)}{x} - \frac{G(y)}{y}\right)(G(x) - G(y)) \le 0$ for $x, y \ge 0$. An example is $G(x) = x/(1+\theta x)$ with $\theta > 0$.

Define the constant-delay basic reproduction number and the expected survival probability rate (ESPR) of the parasite over its life cycle,

$$
R_0^* = \frac{\beta}{\mu + d + \alpha}, \qquad \mathbb{E}\left(e^{-(\mu_v T_1 + \mu T_2)}\right) = \int_{t_0}^{h_2}\int_{t_0}^{h_1} e^{-\mu_v s - \mu u}f_{T_1}(s)f_{T_2}(u)\,ds\,du \in (0,1].
$$

**Theorem.**
1. *(Well-posedness.)* There is a unique positive solution, $\limsup_{t\to\infty}N(t) \le B/\mu = 1$ for $N = S + E + I + R$, and the set $\{B/(\mu+d) \le N \le B/\mu\}$ is positively invariant.
2. *(Exponential decay estimate.)* Every positive solution satisfies

$$
\limsup_{t\to\infty}\frac{1}{t}\log I(t) \le \beta\,\frac{B}{\mu}\,\mathbb{E}\left(e^{-(\mu_v T_1+\mu T_2)}\right) - (\mu + d + \alpha) = (\mu+d+\alpha)\left(R_0^*\,\mathbb{E}\left(e^{-(\mu_v T_1+\mu T_2)}\right) - 1\right).
$$

3. *(Extinction.)* If either $R_0^* < 1$, or $R_0^* \ge 1$ and $\mathbb{E}\left(e^{-(\mu_v T_1+\mu T_2)}\right) < 1/R_0^*$, then $\limsup_{t\to\infty}\frac1t\log I(t) < -\lambda$ for some $\lambda > 0$, so $I(t) \to 0$ exponentially fast.
4. *(Susceptibles under extinction.)* Under the same conditions the susceptibles are stable in the mean, $\lim_{t\to\infty}\frac1t\int_{t_0}^t S(\xi)\,d\xi = B/\mu = 1$, and the disease-free equilibrium $(S, I) = (1, 0)$ is Lyapunov stable.
5. *(Permanence.)* When an endemic equilibrium $(S_1^*, I_1^*)$ exists (which requires $R_0^* > 1$ and a sufficiently large ESPR), then under additional technical conditions every positive solution satisfies $\liminf_{t\to\infty}I(t) \ge qI_1^*e^{-(\mu+d+\alpha)(\rho+1)h} > 0$ with $h = h_1 + h_2$ and constants $0 < q < 1$, $\rho > 0$, so the infection is strongly permanent for every total delay $h$.

Item 3 shows that a large basic reproduction number does not by itself sustain transmission: if the vector and host are unlikely to survive the two incubation periods, the infection still dies out.

## Depends on

- [SEIR epidemic model](../../seir-epidemic-model/README.md)

## Expansion

For item 2 take the Lyapunov functional $\tilde V(t) = \log I(t) + \beta W(t)$, where $W$ collects the double delay integrals $\int\int f_{T_2}(u)f_{T_1}(s)e^{-(\mu_v s + \mu u)}\int_{t-u}^t S(\theta)G(I(\theta-s))/I(t)\,d\theta\,ds\,du$ and its companion with window $[t-s, t]$. Differentiating along solutions, the delayed incidence terms cancel against the derivatives of $W$, and the bounds $S \le B/\mu$ and $G(I) \le I$ leave $\dot{\tilde V} \le \beta(B/\mu)\mathbb{E}(e^{-(\mu_v T_1+\mu T_2)}) - (\mu+d+\alpha)$; integrating and dividing by $t$ gives the bound. Both conditions in item 3 make the right side negative. Item 4 then follows from integrating the $S$ equation once $I \to 0$ exponentially. Item 5 uses a contradiction argument: if $I$ stays below a fraction of $I_1^*$ on an interval longer than the total delay $h$, the delayed incidence forces $I$ back up, which gives the explicit lower bound.

## Sources

- Divine Wanduku, "Some asymptotic properties of SEIRS models with nonlinear incidence and random delays", arXiv:1809.08951 (2018), Section 2 (model and Assumption 2.1, Definition 2.1), Theorems 3.1–3.3, Lemma 4.1 and Theorem 4.1 (extinction), Theorems 5.1–5.2, Lemma 6.1 and Theorem 6.1 (permanence), <https://doi.org/10.48550/arXiv.1809.08951>. Published version: Divine Wanduku, B. O. Oluyede, Nonlinear Analysis: Modelling and Control 25(3) (2020), 461–481, <https://doi.org/10.15388/namc.2020.25.16660>; locators above refer to the arXiv version.
