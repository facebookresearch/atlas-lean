# Invasion speed of a trait in a spatially advancing F-KPP population

**Model.** Two types $A$ and $B$ with densities $N_A, N_B$ on $\mathbb R$ share logistic growth with carrying capacity $K$; $A$ reverts to $B$ at rate $\beta$ and converts $B$ into $A$ at rate $\gamma$ per encounter:

$$\partial_t N_A = \tfrac12 \partial_{xx}N_A + \alpha N_A(K - N_A - N_B) - \beta N_A + \gamma N_A N_B,$$

$$\partial_t N_B = \tfrac12 \partial_{xx}N_B + \alpha N_B(K - N_A - N_B) + \beta N_A - \gamma N_A N_B.$$

After rescaling, the total $v = (N_A + N_B)/K$ and the trait density $w = N_A/K$ solve

$$\partial_t v = \tfrac12\partial_{xx} v + v(1 - v), \qquad \partial_t w = \tfrac12\partial_{xx} w + \bigl(1 - \tilde\beta - (1 - \tilde\gamma)v - \tilde\gamma w\bigr)w,$$

with $\tilde\beta = \beta/(\alpha K)$, $\tilde\gamma = \gamma/\alpha$ and $1 > \tilde\gamma > \tilde\beta > 0$. Take the advancing population to be the travelling wave $v(t, x) = \omega(x + a - \sqrt2\, t)$ of speed $\sqrt 2$ and $w(0, x) = (1 - \tilde\beta/\tilde\gamma)\mathbf 1_{x \le 0}$.

**Theorem.** Let $a \ge 0$ and

$$u_c = \max\left(\sqrt2 - \frac{\tilde\beta}{\sqrt2\,\tilde\gamma}\Bigl(1 + \sqrt{1 - \tilde\gamma}\Bigr),\; \sqrt{2(\tilde\gamma - \tilde\beta)}\right).$$

For all sufficiently small $\delta > 0$ there are constants $C_1, C_2 > 0$ such that for all large $t$,

$$w(t, u_c t - C_1\log t) > \delta \quad\text{and}\quad w(t, u_c t + C_2\log t + z) < 1/t \ \ \text{for all } z > 0.$$

So the trait invades at speed $u_c$, which for small $\tilde\beta$ strictly exceeds the speed $\sqrt{2(\tilde\gamma - \tilde\beta)}$ it would have in a resident population already at carrying capacity.

## Depends on

- [The minimal speed is the least Fisher–KPP front speed](../../../pattern-formation/fisher-kpp-travelling-waves/is-least-front-speeds.md)

## Expansion

Since $v$ solves an autonomous F-KPP equation, the $w$-equation is a scalar F-KPP equation with a moving, time-dependent growth rate. Ahead of the resident front ($v \approx 0$) the trait grows at rate $1 - \tilde\beta$, behind it at rate $\tilde\gamma - \tilde\beta$. The Feynman–Kac representation expresses $w$ as an expectation over Brownian paths weighted by accumulated growth; the optimal paths either stay behind the front (speed $\sqrt{2(\tilde\gamma - \tilde\beta)}$) or ride at the resident front edge, where low density gives faster growth. Brownian bridge estimates for the time spent ahead of the front give the first branch of $u_c$, confirming the small-$\tilde\beta$ expansion proposed by Venegas-Ortiz, Allen and Evans.

## Sources

- Anton Bovier and Lisa Hartung, "The speed of invasion in an advancing population", Journal of Mathematical Biology 87 (2023), 56, <https://doi.org/10.1007/s00285-023-01989-3>; numbering as in arXiv:2204.11072: Theorem 2.1 and Section 2.
