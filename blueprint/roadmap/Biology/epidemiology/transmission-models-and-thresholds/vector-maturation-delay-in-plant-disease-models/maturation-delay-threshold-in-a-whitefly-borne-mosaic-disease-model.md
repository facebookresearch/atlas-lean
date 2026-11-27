# Maturation-delay threshold in a whitefly-borne mosaic disease model

**Model.** Let $x, y$ be healthy and infected plants, and $v_2, v_3$ susceptible and infected mature vectors (whiteflies). Healthy plants grow logistically with rate $r$ and capacity $k$; plants are removed at rate $\mu$, infected plants additionally at rate $\alpha$. Vectors mature after a fixed delay $\tau$, surviving maturation with probability $e^{-c\tau}$ ($c$ is the vector death rate), and recruitment is Ricker-like with carrying capacity proportional to plant density. Transmission is frequency dependent:

$$\begin{aligned}
\dot x &= r x\Big(1 - \frac{x+y}{k}\Big) - \frac{\lambda x v_3}{x+y} - \mu x, \qquad \dot y = \frac{\lambda x v_3}{x+y} - (\mu + \alpha) y,\\
\dot v_2 &= b\,V(t-\tau)\exp\!\Big(-\frac{V(t-\tau)}{a P(t-\tau)}\Big)e^{-c\tau} - \frac{\beta v_2 y}{x+y} - c v_2, \qquad \dot v_3 = \frac{\beta v_2 y}{x+y} - c v_3,
\end{aligned}$$

with $V = v_2 + v_3$, $P = x + y$, and nonnegative history on $[-\tau, 0]$. Solutions are nonnegative and enter the bounded set $\{x + y \le M,\ v_2 + v_3 \le N\}$.

Write $\bar b = b e^{-c\tau}$. For $r > \mu$ and $\bar b > c$ the disease-free state is $\bar x = k(r - \mu)/r$, $\bar v_2 = a\bar x \ln(\bar b/c)$, and

$$\mathcal{R}_0 = \frac{\beta\lambda\,\bar v_2}{c\,\bar x\,(\alpha + \mu)} = \frac{\beta\lambda\,a\,\ln(\bar b/c)}{c\,(\alpha + \mu)} = \frac{\beta\lambda a\,\big(\ln(b/c) - c\tau\big)}{c(\alpha + \mu)} .$$

**Theorem.**
1. The disease-free equilibrium is stable for $\mathcal{R}_0 < 1$, unstable for $\mathcal{R}_0 > 1$, and undergoes a steady-state bifurcation at $\mathcal{R}_0 = 1$.
2. A biologically feasible endemic equilibrium exists if and only if

$$1 < \mathcal{R}_0 < 1 + \frac{(\beta + c)(r - \mu)}{c\,(\alpha + \mu)};$$

above the upper bound, infection drives the plants, and with them the vectors, extinct.
3. If $\mathcal{R}_0 > 1$ and the endemic equilibrium is stable without delay (Routh–Hurwitz conditions on the $\tau = 0$ characteristic quartic), then it remains stable for all $\tau \ge 0$ when the associated frequency polynomial has no positive real root; otherwise stability can be lost through a Hopf bifurcation at critical delays, producing periodic oscillations.

## Expansion

At the disease-free state the vector population settles where Ricker recruitment balances death, $\ln(\bar b/c) = \bar v_2/(a\bar x)$, so the vector-to-plant ratio is $a\ln(\bar b/c)$; $\mathcal{R}_0$ is the product of infections of plants by one infected vector, $\lambda/c$, and of vectors by one infected plant, $\beta/(\alpha+\mu)$ scaled by the vector-to-plant ratio. Because $\ln(\bar b/c) = \ln(b/c) - c\tau$, longer maturation lowers $\mathcal{R}_0$ linearly, and the disease is eliminated for $\tau > \big(\ln(b/c) - c(\alpha+\mu)/(\beta\lambda a)\big)/c$, while vectors themselves persist only for $\tau < \ln(b/c)/c$. Linearization gives a transcendental characteristic equation $\xi^4 + \sum \sigma_i \xi^{4-i} + e^{-\tau\xi}\sum \eta_i \xi^{4-i} = 0$; substituting $\xi = i\omega$ gives a quartic in $\omega^2$ whose positive roots locate the delay-induced Hopf points. Numerical continuation shows that the maturation delay can both stabilize and destabilize the endemic state.

## Sources

- F. Al Basir, Y. N. Kyrychko, K. B. Blyuss, S. Ray, "Effects of vector maturation time on the dynamics of cassava mosaic disease", Bulletin of Mathematical Biology (2021), model (3)–(4) with invariant region, equilibria (5)–(6), existence condition (7)–(9), characteristic equation (10)–(11), Theorems 1–3, <https://doi.org/10.1007/s11538-021-00921-4>, PMCID PMC8238769.
