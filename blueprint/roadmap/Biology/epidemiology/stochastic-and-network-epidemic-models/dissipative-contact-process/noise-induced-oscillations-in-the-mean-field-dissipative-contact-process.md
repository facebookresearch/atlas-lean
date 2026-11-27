# Noise-induced oscillations in the mean-field dissipative contact process

**Model.** Each of $N$ individuals has an infectivity level $x_i(t) \in [0, 1]$, with $x_i = 0$ meaning healthy. A healthy individual becomes infected, jumping to $x_i = 1$, at rate $\lambda v_N(t)$, where $v_N = \frac1N\sum_j x_j$ is the mean infectivity; while infected, its infectivity decays deterministically, $\dot x_i = -\alpha x_i$ (dissipation); and it recovers, jumping to $0$, at rate $r$. Let $m_N = \frac1N\#\{i : x_i > 0\}$ be the infected fraction.

**Theorem.**
1. *(Propagation of chaos.)* For i.i.d. initial states, as $N \to \infty$ each $x_i$ converges to an independent copy of the nonlinear (McKean–Vlasov) process driven by its own mean infectivity, and $(m_N, v_N)$ converges to the solution of the corresponding deterministic mean-field ODE; the fluctuations $\sqrt N(m_N - m, v_N - v)$ converge to a Gaussian diffusion.
2. *(Noise-induced oscillations.)* Let $(m^*, v^*)$ be the endemic equilibrium, start from i.i.d. states with $\mathbb P(x_i(0) > 0) = m^*$ and $\mathbb E[x_i(0)] = v^*$, take $\alpha_N = \rho\lambda_N$ with $0 < \rho < 1$, $\lambda_N \to \infty$ and $\sqrt{\lambda_N}/\log N \to 0$. Then the rescaled fluctuations

$$\hat\xi^N(t) = \sqrt N\,\frac{m_N(t/\sqrt{\lambda_N}) - m^*}{\lambda_N^{1/4}}, \qquad \hat\eta^N(t) = \lambda_N^{1/4}\sqrt N\bigl(v_N(t/\sqrt{\lambda_N}) - v^*\bigr)$$

converge on every $[0, T]$ to the randomly forced harmonic oscillator

$$d\hat\xi = \rho\,\hat\eta\,dt, \qquad d\hat\eta = -\frac{r}{\rho}(1 - \rho)\hat\xi\,dt + r(1 - \rho)\,dW, \qquad \hat\xi(0) = \hat\eta(0) = 0.$$

The finite system therefore oscillates around the endemic state with an almost deterministic period $2\pi/\sqrt{r(1-\rho)}$ (in the time unit $1/\sqrt{\lambda_N}$) and a randomly varying amplitude, although the deterministic limit converges to equilibrium.

## Expansion

When infection and dissipation are fast ($\lambda_N, \alpha_N \to \infty$ with fixed ratio $\rho$), the linearization of the mean-field ODE at the endemic equilibrium has eigenvalues close to a purely imaginary pair, i.e. the equilibrium is a weakly damped focus. Finite-size noise of order $N^{-1/2}$ continually excites this focus; rescaling time and amplitude so that the damping disappears in the limit yields an undamped linear oscillator driven by Brownian noise. This mechanism is a stochastic-amplification explanation of recurrent epidemic waves without seasonal forcing.

## Sources

- Paolo Dai Pra and Elisa Marini, "Noise-induced oscillations for the mean-field dissipative contact process", Electronic Journal of Probability 30 (2025), 1–31, <https://doi.org/10.1214/25-ejp1358>; numbering as in arXiv:2403.03783: Theorems 2.1, 3.1, 4.1 and 5.1.
