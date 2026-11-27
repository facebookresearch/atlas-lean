# Extinction from negative weighted invasion rates

Let $X(t) = (X_1(t), \dots, X_n(t)) \in \mathbb{R}_+^n$ be species densities and $Y(t) \in \mathbb{R}^{\kappa_0}$ an auxiliary
variable (feedbacks, forcing, structure), driven by i.i.d. environmental states $\xi(0), \xi(1), \dots$ in a Polish space $\Xi$:

$$X_i(t+1) = X_i(t)\, F_i(X(t), Y(t), \xi(t)), \quad i = 1, \dots, n, \qquad Y(t+1) = G(X(t), Y(t), \xi(t)).$$

Assume each fitness $F_i(z, \xi)$ is strictly positive, continuous in $z = (x,y)$ and jointly measurable, $G$ is continuous in $z$ and
measurable, and there is a Lyapunov function $V : S \to \mathbb{R}_+$ on $S = \mathbb{R}_+^n \times \mathbb{R}^{\kappa_0}$ with
$V(x,y) \ge |x|^{\gamma_1} + 1$, $V(z) \to \infty$ as $|z| \to \infty$, and
$E[V(x \circ F(z,\xi), G(z,\xi))\, h(z,\xi)] \le \rho V(z) + C$ for some $\rho \in (0,1)$, $C, \gamma_1, \gamma_3 > 0$, where
$h(z,\xi) = \bigl(\max_i \max\{F_i(z,\xi), F_i(z,\xi)^{-1}\}\bigr)^{\gamma_3}$ and $\circ$ is the Hadamard product. Let
$S_0 = \{ \min_i x_i = 0 \}$ be the extinction set. For an ergodic invariant probability measure $\mu$ of $Z = (X, Y)$, its species
support is $S(\mu) = \{ i : \mu(x_i > 0) = 1 \}$ and the **invasion rate** of species $i$ is

$$r_i(\mu) = \int_S E[\log F_i(z, \xi(1))]\, \mu(dz).$$

It exists, is finite, and $r_i(\mu) = 0$ for every $i \in S(\mu)$. Let $\mathcal M$ be the set of ergodic invariant probability measures
supported on $S_0$.

Write $P V(z) = E_z V(Z(1))$, and call $\tilde z$ *accessible* from $z$ if for every neighbourhood $U$ of $\tilde z$ some $k \ge 0$ has
$\Pr_z(Z(k) \in U) > 0$. Assume in addition (Assumption 2.2 of the source) that there are $\phi : S \to (0,\infty)$ and constants
$C, \delta_\phi > 0$ such that for all $z \in S$

$$E_z V(Z(1)) \le V(z) - \phi(z) + C$$

and

$$E_z\bigl(V(Z(1)) - P V(z)\bigr)^2 + E\,\bigl|\log F(z, \xi(1)) - E \log F(z, \xi(1))\bigr|^2 \le \delta_\phi\, \phi(z),$$

where $\log F = (\log F_1, \dots, \log F_n)$ and $|\cdot|$ is the Euclidean norm. Assume also that $S_0$ is *accessible*: from every
$z \in S \setminus S_0$ some point of $S_0$ is accessible.

**Theorem (extinction).** If there are $p_1, \dots, p_n > 0$ such that

$$\sum_{i=1}^n p_i\, r_i(\mu) < 0 \quad \text{for every } \mu \in \mathcal M,$$

then there is a constant $\alpha > 0$, not depending on the initial state, such that for every $z \in S$ (with $\log 0 = -\infty$)

$$\Pr_z\Bigl( \limsup_{t\to\infty} \frac{\log \min_i X_i(t)}{t} \le -\alpha \Bigr) = 1,$$

i.e. with probability one at least one species goes extinct exponentially fast. The bound is one-sided: from $z \in S_0$ some $X_i$
stays zero, so the left side is $-\infty$, and from interior starts the process may approach different boundary ergodic measures with
different negative exponents, so no common exact limit is asserted.

## Expansion

The weighted sum $\sum_i p_i \log X_i(t)$ has asymptotic per-step drift $\sum_i p_i r_i(\mu)$ whenever the process is near the boundary and
distributed approximately like $\mu$; a uniformly negative value for all boundary ergodic measures makes the boundary attracting, and
accessibility guarantees the process gets close enough for this drift to take over. Refinements in the paper identify which subcommunity survives. For $I \subseteq \{1, \dots, n\}$ let $S^I = \{(x, y) \in S : x_i = 0 \text{ for } i \notin I\}$, $S_0^I = \{z \in S^I : \prod_{j \in I} x_j = 0\}$ and $S_+^I = S^I \setminus S_0^I$, and let $\mathcal M^{I,+}$ and $\mathcal M^{I,\partial}$ be the ergodic invariant probability measures giving full mass to $S_+^I$ and to $S_0^I$. Say $I \in \mathcal E^1$ if $\mathcal M^{I,+} \ne \emptyset$, every $\mu \in \operatorname{Conv}(\mathcal M^{I,+})$ has $\max_{i \notin I} r_i(\mu) < 0$ (no outsider can invade the resident face), and, when $I \ne \emptyset$, every $\nu \in \operatorname{Conv}(\mathcal M^{I,\partial})$ has $\max_{i \in I} r_i(\nu) > 0$ (the face's own boundary repels). Under Assumptions 2.1 and 2.2, for each $I \in \mathcal E^1$ other than $\{1, \dots, n\}$ there is $\alpha_I > 0$ such that for every compact $K_I \subset S_+^I$, $\Pr_z\bigl(\limsup_{t\to\infty} t^{-1}\log X_i(t) \le -\alpha_I \text{ for all } i \notin I\bigr) \to 1$ as $z \to K_I$ with $z \in S \setminus S_0$. (Hening, Nguyen and Chesson 2021, Assumption 2.2, Definition 2.1 and Theorems 2.4–2.5.) This page shares its setting and invasion rates with [stochastic persistence from positive invasion rates](persistence-from-positive-invasion-rates.md), the opposite criterion, but does not use that result.

## Sources

- A. Hening, D. H. Nguyen, and P. Chesson, "A general theory of coexistence and extinction for stochastic ecological communities", Journal of Mathematical Biology 82 (2021), article 56, <https://doi.org/10.1007/s00285-021-01606-1>.
