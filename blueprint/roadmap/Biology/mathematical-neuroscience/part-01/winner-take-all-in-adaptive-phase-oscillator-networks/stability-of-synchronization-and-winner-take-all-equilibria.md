# Stability of synchronization and winner-take-all equilibria in a star network of adaptive phase oscillators

A central oscillator (CO) with phase $\theta_0$ and adaptive natural frequency $\omega_0$ is coupled to $n$ peripheral oscillators (POs) with phases $\theta_i$, natural frequencies $\omega_i$ and adaptive connection strengths $a_i$:

$$\dot\theta_0 = \omega_0 + \frac{1}{n}\sum_{j=1}^{n} a_j f(\theta_j - \theta_0), \qquad \dot\theta_i = \omega_i + b\,g(\theta_0 - \theta_i),$$

$$\dot\omega_0 = \frac{\alpha}{n}\sum_{j=1}^{n} a_j f(\theta_j - \theta_0), \qquad \dot a_i = \beta\big(-a_i + c + \gamma\,h(\theta_i - \theta_0)\big),$$

with $\alpha, \beta, \gamma, c > 0$ and $b \in \mathbb{R}$. The functions are $2\pi$-periodic; $f$ and $g$ are odd with $f'(0) > 0$, $f'(\pi) = 0$, $g'(0) > 0$, $g'(\pi) < 0$ and no zeros in $(0, \pi)$; $h$ is even, monotone on $[0, \pi]$, $0 \le h \le 1$, $h(0) = 1$, $h(\pi) = 0$, $h'(0) = h'(\pi) = 0$.

Assume identical POs, $\omega_i = \omega$. In phase differences $\phi_i = \theta_i - \theta_0$ the system has the equilibria $P_k = (\Phi_k, \omega, \Psi_k)$, $k = 0, \dots, n$, where $\Phi_k$ has $k$ entries $0$ and $n - k$ entries $\pi$, and $\Psi_k$ has the corresponding $k$ entries $c + \gamma$ and $n - k$ entries $c$ (with $\binom{n}{k}$ copies of each by permutation symmetry). $P_n$ is full in-phase synchronization; $P_1$ is a winner-take-all (WTA) state in which exactly one PO is in phase with the CO at amplitude $c + \gamma$ and all others are in antiphase at amplitude $c$.

**Theorem.** For identical POs, either $P_n$ is the stable equilibrium ($b > 0$), or the $n$ WTA points $P_1$ are stable while the no-winner point $P_0$ is stable along $2n$ directions and neutral along one ($b < 0$); every $P_k$ with $2 \le k \le n - 1$ is a saddle for all parameter values. Precisely, for $n \ge 2$,

- $P_n$ is stable if $b > 0$, $(c+\gamma) f'(0) + b\,g'(0) > 0$ and $\alpha (c+\gamma) f'(0) > 0$;
- $P_1$ is stable if $b < 0$, $(c+\gamma) f'(0) + n\,b\,g'(0) > 0$ and $\alpha (c+\gamma) f'(0) > 0$.

In particular, when $f'(0) = \nu$ and $g'(0) = 1$, the WTA points are stable exactly for $-(c+\gamma)\nu/n < b < 0$, so for $b < 0$ and $n \ge -(c+\gamma)\nu/b$ no stable WTA point exists. Andronov-Hopf bifurcation of $P_k$ occurs when $k(c+\gamma) f'(0) + n b\,g'(0) = 0$.

**Amplitude bound.** For every $\varepsilon > 0$ and every initial condition there is $t_1$ such that $c - \varepsilon \le a_i(t) \le c + \gamma + \varepsilon$ for all $t > t_1$ and all $i$.

## Expansion

At $P_k$ the conditions $h'(0) = h'(\pi) = 0$ and $f(0) = f(\pi) = 0$ make the Jacobian block-triangular: the amplitude equations contribute the eigenvalue $-\beta$ with multiplicity $n$, and the remaining $(n+1) \times (n+1)$ phase-frequency block uses $f'(\pi) = 0$, so antiphase POs do not act on the CO. Its eigenvalues are $-b\,g'(0)$ with multiplicity $k - 1$ (transverse to the in-phase cluster), $-b\,g'(\pi)$ with multiplicity $n - k$ (the antiphase POs), and the pair

$$\lambda_{\pm} = -\frac{1}{2n}\Big(k(c+\gamma)f'(0) + n b\,g'(0) \pm \sqrt{\big(k(c+\gamma)f'(0) + n b\,g'(0)\big)^2 - 4nk\,\alpha (c+\gamma) f'(0)}\Big)$$

for the cluster mean and $\omega_0$; for $P_0$ the pair is replaced by a single zero eigenvalue. Since $g'(0) > 0 > g'(\pi)$, the eigenvalues $-b\,g'(0)$ and $-b\,g'(\pi)$ have opposite signs, so any $P_k$ with both an in-phase cluster of size at least $2$ and at least one antiphase PO is a saddle; stability is possible only for $k = n$ (needs $b > 0$) or $k \le 1$ (needs $b < 0$), with the stated conditions making the pair stable. The amplitude bound follows from solving the linear amplitude equation with $0 \le h \le 1$. The condition $f'(\pi) = 0$ is what limits the stable regimes to global synchronization, WTA and no-winner.

## Sources

- O. Burylko, Y. Kazanovich, R. Borisyuk, Winner-take-all in a phase oscillator system with adaptation, Scientific Reports (2018), Model formulation, Propositions 1 to 3 and the Appendix (Lemmas 1 to 4). <https://doi.org/10.1038/s41598-017-18666-3> PMCID: PMC5765106
