# Persistence and positive equilibria of the biofilm chemostat

**Model.** In a chemostat whose wall biofilm $w$ occupies volume, the fluid volume shrinks and the dilution rate becomes $D(w) = D_0 w_0/(w_0 - w)$, with $w_0$ the biofilm capacity, so $D(w) \to \infty$ as $w \uparrow w_0$. In dimensionless form, with nutrient $S$, planktonic biomass $u$, wall biomass $w$, uptake functions $f, g$ ($C^1$, increasing, $f(0) = g(0) = 0$; Monod $g(S) = m_2 S/(a_2 + S)$ in the examples), adhesion rate $\alpha$ and sloughing rate $\beta$, the model is $\dot S = D(w)(1-S) - f(S)u - g(S)w$, $\dot u = (f(S) - D(w))u - \alpha u + \beta w$, $\dot w = (g(S) - \beta)w + \alpha u$ with $D(w) = w_0/(w_0 - w)$. Multiplying the vector field by $(1 - w/w_0)$ gives the **rescaled system**

$$\dot S = 1 - S - \Big(1 - \tfrac{w}{w_0}\Big)[u f(S) + w g(S)],\quad \dot u = -u + \Big(1 - \tfrac{w}{w_0}\Big)[(f(S) - \alpha)u + \beta w],\quad \dot w = \Big(1 - \tfrac{w}{w_0}\Big)[\alpha u + (g(S) - \beta)w]$$

on $\Omega = \{0 \le S \le 1,\ u \ge 0,\ 0 \le w \le w_0\}$, which is well posed (Theorem 2.1), has the same orbits and equilibria in $\{w < w_0\}$, and has exactly two boundary equilibria: washout $E_0 = (1,0,0)$ and the **clogged state** $E_w = (1,0,w_0)$. Let $A = f(1) - 1 - \alpha$, $B = g(1) - \beta$.

**Theorem 5.6.** If $E_0$ is unstable, the rescaled system is uniformly strongly $\rho$-persistent for $\rho(S,u,w) = u + w$: there is $\gamma > 0$ with $\liminf_{t\to\infty}(u + w) > \gamma$ for every solution with $u(0) + w(0) > 0$.

**Theorem 5.9.** If both $E_0$ and $E_w$ are unstable, the rescaled system is uniformly persistent: there is $\eta > 0$ with $w(t) < w_0 - \eta$ eventually, and $\liminf u(t) > 0$, $\liminf w(t) > 0$, so the reactor neither washes out nor clogs.

**Positive equilibria.** At a positive equilibrium $E_c = (S, u, w)$ one has $u = 1 - S$ and $w = w(S) = \alpha(1-S)/(\beta - g(S))$ with $g(S) < \beta$, and the equilibria are the roots in $(0,1)$ (with $0 < w(S) < w_0$) of

$$F(S) = (\beta - g(S))\big[f(S) - D(w(S))\big] + \alpha g(S).$$

- **Theorem 6.1.** A positive equilibrium $E_c = (S,u,w)$ is locally exponentially stable if $F'(S) > 0$ and unstable if $F'(S) < 0$.
- **Theorem 6.2.** If $E_0$ is unstable and $\beta > m_2/a_2$, there is a unique positive equilibrium $E_c$, and it is locally exponentially stable.
- **Theorem 6.3.** If $\beta < g(1)$ and $w_0$ is sufficiently large, there are at least two positive equilibria (roots of $w_0 = \Phi(S)$, with $\Phi$ as below).

In the regime of Theorem 6.3 the clogged state is also stable, giving bistability: some initial conditions clog the chemostat in finite time, others converge to a stable operating equilibrium.

## Depends on

- [Washout and clogging in a chemostat with biofilm-driven dilution](washout-and-clogging-in-the-biofilm-chemostat.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

Persistence uses the Smith–Thieme theory: instability of $E_0$ gives uniform weak, then strong, persistence of $\rho = u + w$ (the Butler–McGehee lemma excludes approach to $E_0$); a modified system in $r = w_0 - w$ gives persistence away from the clogged plane when $E_w$ is unstable; combining the two lower bounds in the $u$ and $w$ equations gives explicit positive $\liminf$ bounds. For equilibria, writing $F(S) = 0$ as $D(w(S)) = \phi(S) := f(S) + \alpha g(S)/(\beta - g(S))$ and solving for the capacity gives $w_0 = \Phi(S) := w(S)\phi(S)/(\phi(S) - 1)$. If $\beta > m_2/a_2 > g(1) \ge g(S)$ for all $S$, $\Phi$ is monotone on the relevant interval and the root is unique; if $\beta < g(1)$, $\Phi$ blows up at both ends of $(S_1, S_2)$ with $S_2 = g^{-1}(\beta)$, so large $w_0$ crosses it twice. Local stability is read from the Routh–Hurwitz conditions of the cubic characteristic polynomial, whose constant term carries the sign of $F'(S)$; at a root of $F$ the sign of $F'$ is tied to the slope of $\Phi$, so in Theorem 6.3 the root with $\Phi' < 0$ is stable and the one with $\Phi' > 0$ unstable.

## Sources

- Xiaochen Duan and Sergei S. Pilyugin, "A Chemostat Model with Variable Dilution Rate Due to Biofilm Growth", SIAM Journal on Applied Mathematics 85 (2025), 2295–2317, <https://doi.org/10.1137/24m1704890>; numbering as in arXiv:2411.05213: Theorems 2.1, 3.1, 3.2, 4.3, 5.6, 5.9, 6.1, 6.2, 6.3 and Lemmas 4.1, 4.2.
