# Infection concentrates at the highest-risk points of the diffusive SIS model with conserved population

On $(0, L)$ with homogeneous Neumann boundary conditions, consider the mass-action SIS reaction-diffusion system

$$S_t - d_S S_{xx} = -\beta(x) S I + \gamma(x) I, \qquad I_t - d_I I_{xx} = \beta(x) S I - \gamma(x) I,$$

with positive constants $d_S, d_I$ and positive Hölder continuous $\beta, \gamma$ on $[0, L]$. The total population $N = \int_0^L (S + I)\,dx$ is conserved. An endemic equilibrium (EE) is a positive solution of the steady-state system with $\int_0^L (S + I)\,dx = N$. Let

$$k(x) = \frac{\gamma(x)}{\beta(x)}, \qquad k_{\min} = \min_{[0, L]} k, \qquad \Theta_k = \{x \in [0, L] : k(x) = k_{\min}\},$$

the risk function, its minimum and the set of highest-risk points.

**Theorem.** Assume $k$ is non-constant and $k_{\min} < N/L$. As $d_I \to 0$, every EE $(S, I)$ satisfies $S \to k_{\min}$ uniformly on $[0, L]$. Moreover:

1. If $\Theta_k = \{x_0\}$, then $I \to (N - L k_{\min})\,\delta_{x_0}$ weakly, i.e. $\int_0^L I \zeta\,dx \to (N - L k_{\min})\zeta(x_0)$ for all $\zeta \in C([0, L])$, and $I \to 0$ locally uniformly on $[0, L] \setminus \{x_0\}$.
2. If $\Theta_k = [\varrho_1, \varrho_2]$ with $0 < \varrho_1 < \varrho_2 < L$, then $I \to 0$ uniformly on $[0, \varrho_1] \cup [\varrho_2, L]$ and $I \to \hat I$ uniformly on $[\varrho_1, \varrho_2]$, where $\hat I \in C^2([\varrho_1, \varrho_2])$, $\hat I > 0$ in $(\varrho_1, \varrho_2)$, is the unique positive solution of

$$-\hat I_{xx} = \frac{\beta(x)}{d_S}(\hat a - \hat I)\hat I \ \text{ in } (\varrho_1, \varrho_2), \qquad \hat I(\varrho_1) = \hat I(\varrho_2) = 0, \qquad \int_{\varrho_1}^{\varrho_2} \hat I\,dx = N - L k_{\min},$$

and the constant $\hat a > 0$ is determined by the integral constraint.

Thus, when infected individuals barely move, the susceptible density flattens to the minimum risk value and all of the infection mass $N - L k_{\min}$ sits on the highest-risk set.

## Expansion

Adding the steady-state equations gives $(d_S S + d_I I)_{xx} = 0$ with Neumann data, so $d_S S + d_I I$ is a constant. Wherever $I$ stays of order one this forces $S$ to a constant; the $I$ equation $-d_I I_{xx} = \beta(S - k) I$ with $d_I \to 0$ then rules out positive mass where $S > k$, and a sub/super-solution comparison shows $S$ cannot stay above $k_{\min}$. Mass conservation gives the total infected mass $N - L k_{\min}$, which concentrates where $k = k_{\min}$. On an interval of highest risk, writing $S = (C - d_I I)/d_S$ and dividing the $I$ equation by $d_I$ gives the logistic limit problem with $\hat a = \lim (C - d_S k_{\min})/d_I$. This sharpens an earlier result that only gave $\min k \le \hat S \le \max k$ and an unidentified limiting Radon measure.

## Sources

- R. Peng, Z.-A. Wang, G. Zhang and M. Zhou, Novel spatial profiles of some diffusive SIS epidemic models, *J. Math. Biol.* (2023), <https://doi.org/10.1007/s00285-023-02013-4>; preprint arXiv:2301.01012. Journal version: Theorem 1.1 (earlier result) and Theorem 2.1, equations (2.1)-(2.2) (equations (2.7)-(2.8) in the arXiv preprint); the model and the weak convergence are (1.1)-(1.3) of the arXiv preprint.
