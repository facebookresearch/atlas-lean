# Constant enclosed charge gives zero net terminal current

Let $a \le b$ in $\mathbb{R}^3$ (componentwise) and let $B = [a, b] = \{x : a \le x \le b\}$ be the closed box. Its six faces are indexed by $f = 0, \dots, 5$: faces $2k$ and $2k+1$ are normal to coordinate axis $k$, at the lower level $a_k$ and the upper level $b_k$ with outward signs $\epsilon_f = -1$ and $\epsilon_f = +1$. For a vector field $J : \mathbb{R}^3 \to \mathbb{R}^3$, the outward flux through face $f$ is

$$\Phi_f(J) = \int_{R_f} \epsilon_f\, J_{k}\big(\iota_f(u)\big)\, du,$$

where $k$ is the normal axis of $f$, $R_f \subset \mathbb{R}^2$ is the rectangle of the box in the two tangential coordinates, $\iota_f(u)$ is the point of the face with tangential coordinates $u$, and $du$ is two-dimensional Lebesgue measure.

Let $\rho, \dot\rho : \mathbb{R} \times \mathbb{R}^3 \to \mathbb{R}$ be jointly continuous with $\partial_s \rho(s, x) = \dot\rho(s, x)$ for all $s, x$, and let $Q(s) = \int_B \rho(s, x)\, dx$ be the enclosed charge. Fix $t$ and assume $Q(s) = Q(t)$ for all $s$. Suppose $J$ is continuous on $B$ and has Fréchet derivative $J'(x)$ at every point $x$ of the open box $\prod_i (a_i, b_i)$, and $\operatorname{div} J(x) = \sum_{i} \big(J'(x)\, e_i\big)_i$ denotes the divergence computed from $J'$, and that the local continuity law $\dot\rho(t, x) + \operatorname{div} J(x) = 0$ holds for all $x \in B$. If $I_f = \Phi_f(J)$ for every face $f$, then

$$\sum_{f=0}^{5} I_f = 0.$$
