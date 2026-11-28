# Counting equilibria of the $d$-player two-strategy replicator–mutator dynamics

**Setting.** In an infinite population with two strategies at frequencies $x$ and $1-x$, individuals play in random groups of $d \ge 2$. A focal $S_1$ (resp. $S_2$) player facing $k$ co-players of type $S_1$ earns $a_k$ (resp. $b_k$), so $f_1(x) = \sum_{k=0}^{d-1} a_k \binom{d-1}{k} x^k (1-x)^{d-1-k}$ and similarly $f_2$ with $b_k$. With symmetric mutation probability $q \in [0, 1/2]$, the **replicator–mutator equation** is

$$\dot x = q\big[(1-x)f_2(x) - x f_1(x)\big] + x(1-x)\big(f_1(x) - f_2(x)\big).$$

Substituting $t = x/(1-x)$ shows that interior equilibria $x \in (0,1)$ correspond bijectively to positive roots of $P(t) = \sum_{k=0}^{d+1} c_k t^k$, with $c_0 = -q b_0$, $c_1 = (q-1)(a_0 - b_0) - q(d-1)b_1$, $c_k = q a_{k-2}\binom{d-1}{k-2} + (q-1)(a_{k-1} - b_{k-1})\binom{d-1}{k-1} - q b_k\binom{d-1}{k}$ for $2 \le k \le d-1$, $c_d = (q-1)(a_{d-1} - b_{d-1}) + q(d-1)a_{d-2}$, and $c_{d+1} = q a_{d-1}$.

**Theorem.**
1. (Descartes bound, Lemma 2.5) The number of equilibria equals the number of sign changes of $(c_0,\ldots,c_{d+1})$ or is smaller by an even number.
2. (Exact count, Corollary 2.8) If $s_n$ is the number of sign changes in the coefficients of $(t+1)^n P(t)$, then $s_n$ is non-increasing and the number of equilibria is $N = \lim_{n\to\infty} s_n$.
3. (Two-player social dilemmas, Section 2.2) For $d = 2$ with payoffs $a_{11} = 1$, $a_{22} = 0$, $a_{21} = T \in [0,2]$, $a_{12} = S \in [-1,1]$ and $0 < q < 1/2$, the equilibria are $x = 0$ and the roots in $(0,1]$ of $h(x) = (T+S-1)x^2 + (1-T-2S+q(S-1-T))x + S + q(T-S)$, with $h(1) = -q < 0$. Hence the Snowdrift game ($2 \ge T > 1 > S > 0$) always has exactly two equilibria, the unstable $x = 0$ and a stable interior one, and the Harmony game has one or two.
4. (Random games, Propositions 3.2–3.3) If the $a_k, b_k$ are independent standard Gaussians, the expected number of equilibria is

$$E = \frac{1}{\pi}\int_0^\infty \frac{\sqrt{A(t)M(t) - B(t)^2}}{M(t)}\,dt \quad (q \ne \tfrac12), \qquad E = 1 + \frac{1}{\pi}\int_0^\infty \frac{\sqrt{A(t)M(t) - B(t)^2}}{M(t)}\,dt \quad (q = \tfrac12),$$

where $M(t) = H(t,t)$, $A(t) = \partial^2_{xy}H|_{x=y=t}$, $B(t) = \partial_x H|_{x=y=t}$ and $H(x,y) = \sum_{k,l} \operatorname{Cov}(c_k,c_l)\,x^k y^l$ (for $q = 1/2$, $H$ is the explicit sum given in Proposition 3.3).

## Expansion

Mutation moves the equilibria off the boundary, since for $q > 0$ the boundary points $x=0$ and $x=1$ are in general no longer fixed, and turns counting equilibria into counting positive roots of a polynomial of degree $d+1$. Multiplying by $(t+1)^n$ does not change the positive roots but eventually removes every spurious sign change (Theorem 2.7, due to Avendaño; Theorem 2.9 bounds the power needed when there is no positive root), giving an exact algorithm. The random-game formula is the Edelman–Kostlan expected number of positive roots of a Gaussian polynomial with covariance $\operatorname{Cov}(c_k,c_l)$, which is tridiagonal here because each $c_k$ involves only payoff indices $k-2$, $k-1$, $k$. For $q = 1/2$ the point $x = 1/2$ is always an equilibrium, which accounts for the extra $1$. Comparing with the replicator equation ($q = 0$) quantifies how mutation changes the number of coexistence states.

## Sources

- Manh Hong Duong and The Anh Han, "On equilibrium properties of the replicator–mutator equation in deterministic and random games", arXiv:1904.09805 (2019), Sections 2.2–2.3 and 3.2, Lemmas 2.3 and 2.5, Theorem 2.7, Corollary 2.8, Theorem 2.9, Theorem 3.1, Propositions 3.2–3.3, <https://doi.org/10.48550/arXiv.1904.09805>. Published version: Dynamic Games and Applications 10 (2019) 641–663, <https://doi.org/10.1007/s13235-019-00338-8>.
