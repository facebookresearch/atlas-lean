# Free-boundary limit of the diffusive SIS model with recruitment and disease death

On $(0, L)$ with Neumann boundary conditions, consider the SIS system with recruitment and disease-induced death
$$S_t - d_S S_{xx} = \Lambda - S - \beta(x) S I + \gamma(x) I, \qquad I_t - d_I I_{xx} = \beta(x) S I - (\gamma(x) + \eta(x)) I,$$
with a constant $\Lambda > 0$ and positive Hölder continuous $\beta, \gamma, \eta$. The disease-free equilibrium is $(\Lambda, 0)$. Let
$$h(x) = \frac{\gamma(x) + \eta(x)}{\beta(x)}, \qquad h_{\min} = \min_{[0, L]} h, \qquad \Theta_h = \{x : h(x) = h_{\min}\},$$
and assume $\Lambda > h(x)$ for all $x \in [0, L]$.

**Theorem.** As $d_I \to 0$, along a subsequence every endemic equilibrium $(S, I)$ satisfies $S \to \hat S$ uniformly on $[0, L]$ and $I \to \mu$ weakly for a Radon measure $\mu$, where $\hat S$ solves weakly in $W^{1,2}(0, L)$ the free-boundary problem
$$-d_S \hat S_{xx} = \Lambda - \hat S - \eta(x)\, \mu\big|_{\{x \in [0, L] : \hat S(x) = h(x)\}} \quad \text{in } (0, L).$$
Moreover:

1. $\mu(\{x : \hat S(x) \ne h(x)\}) = 0$ and $\mu(\{x : \hat S(x) = h(x)\}) > 0$;
2. $\hat S \in C([0, L])$, $h_{\min} \le \hat S \le h$ on $[0, L]$, and $\Theta_h \subset \{x : \hat S(x) = h(x)\}$;
3. if $x_1 < x_2$ are consecutive points of $\Theta_h$, i.e. $(x_1, x_2) \cap \Theta_h = \emptyset$, then $\hat S > h_{\min}$ on $(x_1, x_2)$.

So the infection is supported on the contact set where $\hat S$ touches the risk function $h$, which contains every highest-risk point but may be much larger. In contrast with the conserved model, $\hat S$ is non-constant unless $h$ is constant.

## Depends on

- [Infection concentrates at the highest-risk points of the diffusive SIS model with conserved population](infection-concentrates-at-highest-risk-points-in-the-conserved-sis-model.md)

## Expansion

The $I$ equation reads $-d_I I_{xx} = \beta (S - h) I$. As $d_I \to 0$, positive infected mass can survive only where $S$ is pushed down to $h$, while $S \le h$ holds in the limit because a region with $S > h$ would make $I$ grow. Adding the equations gives $-(d_S S + d_I I)_{xx} = \Lambda - S - \eta I$, and passing to the limit yields the obstacle-type problem for $\hat S$, with the measure $\eta\mu$ acting only on the contact set. Integrating over $(0, L)$ shows the total infected mass is positive, so the contact set has positive $\mu$-measure.

## Sources

- R. Peng, Z.-A. Wang, G. Zhang and M. Zhou, Novel spatial profiles of some diffusive SIS epidemic models, *J. Math. Biol.* (2023), <https://doi.org/10.1007/s00285-023-02013-4>; preprint arXiv:2301.01012. Theorem 1.2 (earlier result), Theorem 2.2, equations (1.4)-(1.6), (2.9)-(2.14).
