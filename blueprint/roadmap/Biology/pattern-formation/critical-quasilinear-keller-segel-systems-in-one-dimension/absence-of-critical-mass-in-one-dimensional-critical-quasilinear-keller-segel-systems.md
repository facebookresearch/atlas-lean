# Absence of critical mass in one-dimensional critical quasilinear Keller–Segel systems

**Setting.** Let $m \in \mathbb{R}$, $\tau, k \in \{0,1\}$ with $(\tau,k) \in \{(0,0),(0,1),(1,1)\}$ (Jäger–Luckhaus, parabolic–elliptic and fully parabolic settings), and consider on $(0,1)\times(0,T)$ with homogeneous Neumann conditions

$$u_t = \big(D(u)u_x - S(u)v_x\big)_x, \qquad \tau v_t = v_{xx} - k v - (1-k)M + u,$$

where $D(\sigma) = (\sigma+1)^{m-1}$, $S(\sigma) = \sigma(\sigma+1)^m$ for $\sigma \ge 0$, and $M = \int_0^1 u_0$. The ratio $S(u)/D(u) \sim u^2$ for large $u$, which is the critical growth $u^{2/n}$ for $n = 1$. Initial data satisfy $u_0, \tau v_0 \in \bigcup_{\theta>1} W^{1,\theta}((0,1))$, $0 \not\equiv u_0 \ge 0$, $\tau v_0 \ge 0$.

**Theorem.** Let $(u,v)$ be the maximal classical solution.
1. *(Small mass.)* If $m > 0$, there is $\varepsilon > 0$ such that $\int_0^1 u_0 < \varepsilon$ implies that the solution is global and bounded uniformly in time, in all three settings.
2. *(Parabolic–elliptic, any mass.)* If $\tau = 0$, $k \in \{0,1\}$ and $m > 0$, the solution is global and uniformly bounded for all admissible data.
3. *(Jäger–Luckhaus, monotone data.)* If $(\tau,k) = (0,0)$, $m \in \mathbb{R}$ is arbitrary and $u_0$ is nonincreasing, the solution is global and uniformly bounded. By symmetry the same holds for nondecreasing $u_0$ and for data symmetric about $x = \tfrac12$ and monotone on $(0,\tfrac12)$.
4. *(Fully parabolic, strong saturation.)* If $m \le -1$, the solution is global and uniformly bounded for all admissible data in all three settings.

Hence for $m \le -1$ (all settings), and for $m > 0$ (parabolic–elliptic settings), there is no critical mass: no threshold of $\int_0^1 u_0$ separates bounded solutions from blow-up, in contrast with the critical quasilinear Keller–Segel system in dimension $n \ge 2$.

## Depends on

- [ε-regularity criterion for one-dimensional quasilinear Keller–Segel systems](epsilon-regularity-criterion-for-one-dimensional-quasilinear-keller-segel-systems.md)

## Expansion

Each statement is reduced to the ε-regularity criterion, i.e. to excluding concentration of mass at a point. For small mass this is immediate. In the parabolic–elliptic settings the mass accumulation function $w = \int_0^x u$ solves a spatially non-degenerate scalar parabolic equation; pointwise estimates of $v_x$ then give Hölder continuity of $w$, uniformly in time. In the Jäger–Luckhaus case with monotone data, comparison and preservation of monotonicity give the same uniform continuity. For $m \le -1$ the sensitivity $S$ is bounded; the Lyapunov functional stays bounded from below in one dimension, so its dissipation is integrable in time, and together with the embedding $W^{1,1}((0,1)) \hookrightarrow L^\infty((0,1))$ this yields a uniform-in-time $L\log L$ bound on $u$, i.e. uniform integrability.

## Sources

- X. Cao and M. Fuest, "Absence of critical mass phenomena in one-dimensional critical quasilinear Keller–Segel systems", arXiv:2606.18006 (2026), Proposition 1.3, Theorems 1.4, 1.5 and 1.7, and Remark 1.6 (proofs in Sections 3–5), <https://doi.org/10.48550/arXiv.2606.18006>.
