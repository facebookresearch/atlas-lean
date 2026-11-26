# Unique absolutely continuous invariant law of the quiescence-switching hematopoiesis PDMP

**Setting.** Let $(X,I)$ be the PDMP on $\mathbb{R}_+^3\times\{0,1\}$ in which $I$ (the state of a single cancer stem cell: $0$ quiescent, $1$ active) jumps $0\to1$ at rate $a_M>0$ and $1\to 0$ at rate $q_M(x_2,x_3)$, and between jumps $\dot X = g(X,I)$ with

$$
g(x,i) = \big(a-(a+q(x_2,x_3))x_1,\; r(x_2,x_3)x_1 - d x_2,\; r_M(x_2,x_3)\,i - d_M x_3\big)^{\mathsf T},
$$

where $q(x_2,x_3) = q_1+q_2x_2+q_3x_3$, $q_M(x_2,x_3) = q_{1,M}+q_{2,M}x_2+q_{3,M}x_3$, $r(x_2,x_3) = c_1/(1+c_2x_2+c_3x_3)$, $r_M(x_2,x_3) = c_{1,M}/(1+c_{2,M}x_2+c_{3,M}x_3)$, with $a,q_1,q_{1,M},c_1,c_{1,M},d,d_M>0$ and the remaining coefficients $\ge 0$. Here $x_1$ is the active fraction of healthy stem cells and $x_2,x_3$ are rescaled healthy and mutant red-cell numbers.

**Invariant box.** With $B_1 = a/(a+q_1)$, $b_1 = a/\big(a+q_1+q_2c_1/d+q_3c_{1,M}/d_M\big)$ and $b_2 = c_1b_1/\big(d(c_2c_1/d+c_3c_{1,M}/d_M)\big)$, the compact set $B = [b_1,B_1]\times[b_2,c_1/d]\times[0,c_{1,M}/d_M]$ is positively invariant under both flows $g(\cdot,0)$ and $g(\cdot,1)$, and every trajectory enters $B\times\{0,1\}$ in finite time.

**Theorem (ergodicity).** Assume in addition $c_3+q_3>0$, so the healthy dynamics actually feel the mutant red cells. Then $(X,I)$ has a unique invariant probability measure $\pi$; it is absolutely continuous with respect to Lebesgue measure, its support is $\Gamma\times\{0,1\}$ where $\Gamma$ is the closure of the set of points reachable by concatenating the two flows from an explicit point $p = (p_1,p_2,0)\in B$, and there are $C,\gamma>0$ with

$$
\big\|\mathbb{P}\big((X_t,I_t)\in\cdot \mid (X_0,I_0) = (x,i)\big) - \pi\big\|_{TV}\le C e^{-\gamma t}\qquad\text{for all } t\ge0,\ (x,i)\in B\times\{0,1\}.
$$

**Theorem (stationary densities).** Writing $\pi(dx,\{i\}) = h_i(x)\,dx$, the pair $(h_0,h_1)$ is the unique couple of nonnegative integrable functions supported in $B$ with $\int_B(h_0+h_1) = 1$ that weakly solves, on the interior of $B$,

$$
\nabla\cdot\big(h_0\, g(\cdot,0)\big) = q_M(x_2,x_3)h_1 - a_M h_0,\qquad
\nabla\cdot\big(h_1\, g(\cdot,1)\big) = a_M h_0 - q_M(x_2,x_3) h_1 .
$$

## Expansion

The proof follows the Benaïm–Le Borgne–Malrieu–Zitt theory of PDMPs switching between finitely many vector fields. Lemma 2 gives the compact positively invariant set. The accessible point $p$ is the unique stationary point of $g(\cdot,0)$ (cancer cell quiescent, so $x_3\to0$); the planar $(x_1,x_2)$ flow has negative divergence, so by Poincaré–Bendixson and Dulac-type arguments every trajectory of $g(\cdot,0)$ approaches $p$, hence $\Gamma = \overline{\gamma^+(p)}$ (Lemma 3). Since $g(p,0) = 0$, the convex-combination condition at an accessible point holds, and the weak bracket condition (the fields $g(\cdot,0)$, $g(\cdot,1)$ and their iterated Lie brackets span $\mathbb{R}^3$ at a point of $\Gamma$) is verified from $[g(\cdot,0),g(\cdot,1)]$, whose first two components are $-q_3x_1c_{1,M}/T_M$ and $-c_3c_1x_1c_{1,M}/(T^2T_M)$; this is where $c_3+q_3>0$ enters. This yields absolute continuity, uniqueness and exponential convergence in total variation. The stationary system is the weak form of $\int\mathcal{L}f\,d\pi = 0$ after integration by parts; uniqueness of its normalized solution follows from uniqueness of $\pi$.

## Depends on

- [PDMP limit of hematopoiesis with a single quiescence-switching cancer stem cell](pdmp-limit-of-hematopoiesis-with-a-switching-cancer-stem-cell.md)

## Sources

- C. Bonnet, "A PDMP to model the stochastic influence of quiescence dynamics in blood cancers", arXiv:2303.06412 (2023), Section 3 (Lemmas 2–3, Theorem 2) and Section 4 (Theorem 3), <https://doi.org/10.48550/arXiv.2303.06412>.
