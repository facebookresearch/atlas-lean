# Global pseudo-first-order approximation of Michaelis–Menten kinetics

**Setting.** As in the comparison bounds, let $(s, c)$ solve the Michaelis–Menten system
$\dot s = -k_1 e_0 s + (k_1 s + k_{-1}) c$, $\dot c = k_1 e_0 s - (k_1 s + k_{-1} + k_2) c$ from
$(s_0, 0)$, and let $(s^*, c^*)$ solve its linearization at the origin from the same initial value.

**Statement.** Let $\mathcal M$ be a compact subset of the open orthant of parameter vectors
$\pi = (e_0, k_1, k_{-1}, k_2) \in \mathbb{R}^4_{>0}$ and $K^* = \min\{k_2/k_1 : \pi \in \mathcal M\}$.
There is a constant $C$ (of dimension concentration$^{-1}$), depending only on $\mathcal M$, such that
for every $\pi \in \mathcal M$, every $0 < s_0 \le K^*/2$ and **every** $t \in [0, \infty)$,

$$\left|\frac{s(t) - s^*(t)}{s_0}\right| \le C s_0, \qquad \left|\frac{c(t) - c^*(t)}{s_0}\right| \le C s_0.$$

Thus the absolute approximation errors are $O(s_0^2)$ uniformly in time, and the nonlinear solution
converges to the linear one on $[0,\infty)$ as $s_0 \to 0$. The sufficient condition for the
pseudo-first-order approximation is $s_0 \ll K = k_2/k_1$; no smallness of $e_0$ is needed.

## Depends on

- [Kamke comparison bounds for Michaelis–Menten kinetics at low substrate](kamke-comparison-bounds-for-michaelis-menten-at-low-substrate.md)

## Expansion

By the comparison bounds it suffices to show $|s_{\mathrm{up}} - s_{\mathrm{low}}| \le C s_0^2$ and the
same for $c$. Each normalized bound has the form $B_1(s_0,\pi) e^{-A_1(s_0,\pi)t} + B_2(s_0,\pi)
e^{-A_2(s_0,\pi)t}$ with $A_i, B_i$ continuously differentiable on a neighbourhood of
$[0, K^*/2] \times \mathcal M$, and the linear solution is the same expression at $s_0 = 0$. A mean-value
estimate in $s_0$ on the compact parameter set bounds the coefficient differences by a multiple of
$s_0$, and the decay rates stay bounded away from zero, which makes the estimate uniform in $t$. The
point is globality: near the equilibrium the nonlinear system is smoothly equivalent to its
linearization by Sternberg's theorem, but that local fact does not control the whole trajectory from
$(s_0,0)$.

## Sources

- J. Eilertsen, S. Schnell, S. Walcher, "The Michaelis–Menten reaction at low substrate concentrations: pseudo-first-order kinetics and conditions for timescale separation", Bulletin of Mathematical Biology (2024), <https://doi.org/10.1007/s11538-024-01295-z> (PMC11069484). Proposition 2(e) and its proof, Remark 2, Conclusion.
