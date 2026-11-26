# Morse-decomposition criterion for robust permanence

**Setting.** Consider

$$\frac{dx_i}{dt} = x_i f_i(x,y)\ (i = 1,\dots,n), \qquad \frac{dy_j}{dt} = g_j(x,y)\ (j = 1,\dots,m),$$

on $S = \mathbb{R}_+^n \times K$ with $K \subset \mathbb{R}^m$, where $x$ are population densities and $y$ are feedback variables. Assume (S1) $x_if_i$ and $g_j$ are locally Lipschitz and (S2) there is a compact forward-invariant $Q \subseteq S$ that every trajectory eventually enters. Let $z.t$ be the flow, $\Gamma = \omega(Q)$ the global attractor, and $S_0 = \{(x,y) \in S : \prod_i x_i = 0\}$ the (invariant) extinction set. The system is *permanent* if there is $\beta > 0$ with $\liminf_{t\to\infty} x_i(t) \ge \beta$ for all $i$ and all initial $z \in S\setminus S_0$. A $(\delta, Q)$-perturbation $(\tilde f, \tilde g)$ satisfies $|\tilde f_i - f_i| < \delta$, $|\tilde g_j - g_j| < \delta$ on $Q$, the same Lipschitz property, and has $Q$ as a forward-invariant absorbing set; the system is *robustly permanent* if one $\beta$ works for every $(\delta,Q)$-perturbation, for some $\delta > 0$.

A *Morse decomposition* of a compact invariant set $\Gamma'$ is a family of pairwise disjoint isolated compact invariant sets $M_1,\dots,M_\ell$ such that every $z \in \Gamma' \setminus \bigcup_k M_k$ has $\omega(z) \subset M_i$ and $\alpha(z) \subset M_j$ for some $i < j$.

**Theorem.** Let $\{M_1,\dots,M_\ell\}$ be a Morse decomposition of $S_0 \cap \Gamma$.
1. If for each $k$ there are weights $p_{k1},\dots,p_{kn} > 0$ such that every $z \in M_k$ has some $T_z > 0$ with

$$\sum_{i=1}^n p_{ki}\int_0^{T_z} f_i(z.t)\,dt > 0,$$

then the system is permanent, and in fact robustly permanent.
2. (Partial converse.) If for each $k$ there are $p_{ki} > 0$ such that every $z \in M_k$ has $T_z > 0$ with $\sum_i p_{ki}\int_0^{T_z} f_i(z.t)\,dt < 0$, then the system is not permanent; more strongly, $S_0 \cap \Gamma$ is an attractor in $\Gamma$.

## Expansion

The proof passes through *good average Lyapunov functions* (GALFs): continuous $P \ge 0$ on a neighborhood $U$ of a Morse set, vanishing exactly on $S_0$, independent of $y$, with $p_i = (x_i/P)\,\partial P/\partial x_i$ extending continuously to $S_0$ and $\int_0^{T_z}\sum_i p_i f_i(z.t)\,dt > 0$ for every $z \in S_0 \cap U$. For constant weights, $P = \prod_i x_i^{p_{ki}}$ is a GALF, and $\ln P = \sum_i p_{ki}\ln x_i$ grows on average near $M_k$. Compactness gives a finite cover of $M_k$ on which the integral exceeds a fixed $c > 0$ within a bounded time, so each Morse set is isolated in $S$ and attracts no positive orbit; a theorem of Garay (1989) then yields permanence. Strictness of the condition makes it stable under $(\delta,Q)$-perturbations, and a result of Hirsch et al. (2001) gives a uniform $\beta$ for all of them. The converse applies the same argument to the reverse-time flow on $\Gamma$. Permanence alone does not imply robust permanence: $\dot x = x^2(1-x)$ is permanent but not robustly permanent.

## Sources

- S. Patel, S. J. Schreiber, "Robust permanence for ecological equations with internal and external feedbacks", Journal of Mathematical Biology (2018), Eqs. (2)–(5), Definitions 1–2, Theorem 1, Corollary 1, Theorem 2, Definition A1 and Theorem A1, <https://doi.org/10.1007/s00285-017-1187-5>, PMCID PMC5949143.
