# Stochastic persistence from positive invasion rates

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

**Theorem (persistence).** If for every invariant measure $\mu \in \operatorname{Conv}(\mathcal M)$

$$\max_{1 \le i \le n} r_i(\mu) > 0,$$

then the community is *almost surely stochastically persistent*: for every $\varepsilon > 0$ there is $\eta > 0$ such that for every
initial state $z \notin S_0$,

$$\Pr_z\Bigl( \liminf_{t\to\infty} \frac1t \sum_{s=1}^t \mathbf 1\{\min_i X_i(s) > \eta\} > 1 - \varepsilon \Bigr) = 1,$$

and it is *stochastically persistent in probability*: $\liminf_{t\to\infty} \Pr_z(\min_i X_i(t) > \eta) > 1 - \varepsilon$. Write $P^k(z, \cdot)$ for the $k$-step transition kernel of $Z$, and call
$\tilde z$ *accessible* from $z$ if $P^k(z, U) > 0$ for some $k \ge 0$ for every neighbourhood $U$ of $\tilde z$.

**Theorem (uniqueness).** Suppose in addition that there are a point $z^* \in S \setminus S_0$ accessible from every $z \in S \setminus S_0$,
a neighbourhood $U$ of $z^*$, a nonzero measure $\iota$ on $S \setminus S_0$ and a probability measure $\gamma$ on $\{1, 2, \dots\}$ such that
$\sum_{k \ge 1} \gamma(k) P^k(z, \cdot) \ge \iota(\cdot)$ for every $z \in U$. Then there is a unique invariant probability measure $\pi$ on
$S \setminus S_0$, and for every $z \in S \setminus S_0$ the random occupation measures $t^{-1}\sum_{s=1}^t \delta_{Z(s)}$ converge weakly to $\pi$
almost surely. Both requirements matter: a minorization near a point of one closed class of the interior says nothing about another class
that cannot reach it, so without accessibility of $z^*$ from every interior state the interior may carry several invariant laws.

## Expansion

Near the boundary, $\log X_i(t) = \log X_i(0) + \sum_{s<t} \log F_i(Z(s), \xi(s))$, so the long-run growth of a rare species is governed by
the average of $\log F_i$ along the boundary dynamics, i.e. by $r_i(\mu)$ for whatever invariant law $\mu$ the process approximates
while near $S_0$. If every boundary invariant measure, including mixtures of ergodic ones, has some species with positive invasion rate,
one constructs (by a minimax argument over $\operatorname{Conv}(\mathcal M)$) weights $p_i > 0$ with $\sum_i p_i r_i(\mu) > 0$ for all
$\mu \in \mathcal M$, and $-\sum_i p_i \log x_i$ acts as an average Lyapunov function repelling the process from $S_0$. The moment
condition with $h$ prevents violent crashes to low density in one step, which can otherwise break persistence. (Hening, Nguyen and
Chesson 2021, Equations 2.1–2.5, Assumption 2.1, Proposition 2.1 and Theorems 2.1–2.2; extends Benaïm and Schreiber 2019 to
non-compact state spaces.)

## Sources

- A. Hening, D. H. Nguyen, and P. Chesson, "A general theory of coexistence and extinction for stochastic ecological communities", Journal of Mathematical Biology 82 (2021), article 56, <https://doi.org/10.1007/s00285-021-01606-1>.
