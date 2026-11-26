# Wave speed of strong-competition fronts decreases with the diffusion ratio

**Model.** In the Lotka-Volterra competition-diffusion system with strong competition ($k_1, k_2 > 1$), a travelling front $(u,v)(t,x) = (U,V)(x - ct)$ solves

$$U'' + cU' + U(1 - U - k_1V) = 0, \qquad dV'' + cV' + rV(1 - V - k_2U) = 0,$$

with $(U,V)(-\infty) = (1,0)$, $(U,V)(+\infty) = (0,1)$ and $U' < 0 < V'$. Here $d > 0$ is the diffusion ratio of species $v$ to $u$ and $r > 0$ its relative growth rate. For all $k_1,k_2 > 1$, $r,d > 0$ there is a unique speed $c = c_{k_1,k_2,r,d}$ admitting such a front, unique up to translation. $c > 0$ means $u$ invades $v$; $c < 0$ means $v$ invades $u$.

**Theorem.**
1. (Smoothness) The speed and the normalized front ($U(0) = \tfrac12$) depend $C^\infty$-smoothly on $(k_1,k_2,r,d)$.
2. (Monotonicity) If $c \le 0$ and $c(1 - 1/d) \le 0$, then $\partial_d c < 0$; in particular $\partial_d c < 0$ at every standing front. For $k_1 = k_2 = k$: if $d > r$ and $d \ge 1$, or $d = r$, then $\partial_d c_{k,k,r,d} < 0$.
3. (Threshold) For each $k_2 > 1$ there is a unique $C^\infty$, strictly decreasing function $\mathcal{K}(\cdot\,;k_2)$ on $(0,\infty)$ with $c = 0 \iff k_1 = \mathcal{K}(d/r; k_2)$, satisfying $\sqrt{k_2} < \mathcal{K}(\delta;k_2) < k_2^2$, $\mathcal{K}(1;k_2) = k_2$, $\mathcal{K}(\delta;k_2) \to k_2^2$ as $\delta \downarrow 0$ and $\to \sqrt{k_2}$ as $\delta \to \infty$.
4. (Sign of the speed) With $\delta = d/r$: if $k_1 \le \sqrt{k_2}$ then $c > 0$, and if $k_1 \ge k_2^2$ then $c < 0$, for all $d,r$. If $\sqrt{k_2} < k_1 < k_2^2$, there is a unique $\delta^*(k_1,k_2)$ with $c > 0$ for $\delta < \delta^*$, $c = 0$ at $\delta = \delta^*$, $c < 0$ for $\delta > \delta^*$, and $\operatorname{sgn}(\delta^* - 1) = \operatorname{sgn}(k_2 - k_1)$.

## Expansion

Differentiating the front equations in $d$ gives $\mathcal{L}(\partial_d\Phi) + (\partial_d c)\Phi' = -(0, V'')^T$, where $\mathcal{L}$ is the linearization. $\mathcal{L}$ is Fredholm of index zero with kernel spanned by $\Phi' = (U',V')$ and adjoint kernel spanned by $\Psi = (-a,b)$ with $a,b > 0$; pairing with $\Psi$ gives the adjoint identity $\partial_d c = -\int_\mathbb{R} bV''\,d\xi \big/ \int_\mathbb{R}(bV' - aU')\,d\xi$, whose denominator is positive, and a maximum-principle argument fixes the sign of the numerator under the stated conditions. At a standing front the implicit function theorem gives the threshold curve $k_1 = \mathcal{K}(\delta)$ and the explicit formula $\partial_\delta\mathcal{K} = -\int W / (2\delta\int aUV) < 0$. Biologically, faster dispersal of the competitor $v$ helps it invade, at least in the regimes covered.

## Sources

- Cyrille Kenne, "Monotonicity of the propagation speed with respect to the diffusion in a Lotka-Volterra competition-diffusion system", arXiv:2608.27431 (2026), Section 1, Theorems 1.1, 1.3 and 1.4, Corollary 1.2, and Section 2, Proposition 2.2 and Theorem 2.4, <https://doi.org/10.48550/arXiv.2608.27431>.
