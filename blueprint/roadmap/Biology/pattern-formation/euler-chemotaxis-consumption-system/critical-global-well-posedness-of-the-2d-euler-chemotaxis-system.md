# Critical global well-posedness of the 2D Euler-chemotaxis-consumption system

**Model.** Micro-swimmers of density $n \ge 0$ with logistic-type growth, suspended in an ideal fluid with velocity $u$ and pressure $\pi$, follow a chemical $c \ge 0$ that they consume (sign $+$) or produce (sign $-$). On $\mathbb{R}^2$, with gravity $g = (0,-1)$,

$$\begin{aligned}
&\partial_t u + (u\cdot\nabla)u + \nabla\pi = ng, \qquad \operatorname{div} u = 0,\\
&\partial_t n - \Delta n + u\cdot\nabla n + n^3 - n + \operatorname{div}(n\nabla c) = 0,\\
&\partial_t c - \Delta c + u\cdot\nabla c \pm nc = 0.
\end{aligned}$$

**Theorem.** Let $n_0, c_0 \ge 0$ with

$$n_0 \in L^1\cap L^2\cap\dot B^{-1}_{\infty,1}, \qquad c_0 \in L^2\cap\dot B^0_{\infty,2}, \qquad u_0 \in L^2,\ \ \omega_0 = \operatorname{curl}u_0 \in L^{6/5}\cap L^\infty.$$

Then:
1. There is a unique global solution with, for every $T > 0$, $n \in L^\infty_T L^2 \cap L^2_T\dot H^1 \cap L^1_T\dot W^{1,\infty}$, $c \in L^\infty_T(L^2\cap\dot B^0_{\infty,2}) \cap L^2_T(\dot H^1\cap\dot W^{1,\infty})$, and $u \in L^\infty_T L^2$ with $\operatorname{curl}u \in L^\infty_T(L^{6/5}\cap L^\infty)$.
2. In addition $n \in L^\infty_T L^1 \cap L^3_T L^3 \cap L^1_T(\dot W^{1,6/5}\cap\dot B^1_{\infty,1})$ and $c \in L^2_T\dot B^1_{\infty,1}\cap\widetilde{L^\infty_T}(\dot B^0_{\infty,2})$.
3. The solution depends continuously on the initial data on bounded sets of this critical data space.

No free energy is used, so the data need not be positive almost everywhere (only nonnegative), and the conclusions hold for either sign of the reaction term $\pm nc$.

## Expansion

The basic a priori bounds are sign-preserving mass and $L^2$ estimates: $\|n\|_{L^\infty_TL^1} + \|n\|^3_{L^3_TL^3} \lesssim \|n_0\|_{L^1}$ (the cubic absorption $n^3$ supplies the $L^3$ bound) and an exponential-in-time $L^2/\dot H^1$ bound for $c$. Scaling shows these subcritical quantities control the critical interaction terms: they bound $u$ in $L^2$, the vorticity in $L^{6/5}$ and $\nabla n$ in $L^1_TL^{6/5}$, and then the Lipschitz norm of $c$ in Chemin-Lerner spaces. Closing the $L^2$ estimate for $\nabla c$ forces the Besov space $\dot B^0_{\infty,2}$ as the natural critical space for $c_0$; the Lipschitz bound on $\nabla c$ then controls the chemotactic flux $n\nabla c$, and vorticity transport in 2D gives global existence.

## Sources

- Dimitri Cobb, "Critical Well-Posedness of a Euler-Chemotaxis System in 2D", arXiv:2611.14148 (2026), Section 1, Theorem 1, and Section 2, Propositions 8-12, <https://doi.org/10.48550/arXiv.2611.14148>.
