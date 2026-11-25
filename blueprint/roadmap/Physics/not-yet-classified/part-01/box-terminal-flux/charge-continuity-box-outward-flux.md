# Charge continuity for the six faces of a box

Let $a \le b$ in $\mathbb{R}^3$ (componentwise) and let $B = [a, b] = \{x : a \le x \le b\}$ be the closed box. Its six faces are indexed by $f = 0, \dots, 5$: faces $2k$ and $2k+1$ are normal to coordinate axis $k$, at the lower level $a_k$ and the upper level $b_k$ with outward signs $\epsilon_f = -1$ and $\epsilon_f = +1$. For a vector field $J : \mathbb{R}^3 \to \mathbb{R}^3$, the outward flux through face $f$ is

$$\Phi_f(J) = \int_{R_f} \epsilon_f\, J_{k}\big(\iota_f(u)\big)\, du,$$

where $k$ is the normal axis of $f$, $R_f \subset \mathbb{R}^2$ is the rectangle of the box in the two tangential coordinates, $\iota_f(u)$ is the point of the face with tangential coordinates $u$, and $du$ is two-dimensional Lebesgue measure.

Suppose $J$ is continuous on $B$ and has Fréchet derivative $J'(x)$ at every point $x$ of the open box $\prod_i (a_i, b_i)$, and $\operatorname{div} J(x) = \sum_{i} \big(J'(x)\, e_i\big)_i$ denotes the divergence computed from $J'$. Let $\dot\rho : \mathbb{R}^3 \to \mathbb{R}$ be integrable on $B$ and satisfy the local continuity law $\dot\rho(x) + \operatorname{div} J(x) = 0$ for all $x \in B$. Then

$$\sum_{f=0}^{5} \Phi_f(J) = -\int_B \dot\rho(x)\, dx.$$
