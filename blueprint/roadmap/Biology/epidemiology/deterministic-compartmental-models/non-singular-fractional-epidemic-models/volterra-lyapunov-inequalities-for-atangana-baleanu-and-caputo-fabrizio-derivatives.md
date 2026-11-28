# Volterra-type Lyapunov inequalities for Atangana–Baleanu and Caputo–Fabrizio derivatives

**Derivatives.** For $0 < \alpha < 1$, a normalization $B$ with $B(0) = B(1) = 1$, and $f \in H^1(t_0,\infty)$, the Caputo–Fabrizio (CF) and Atangana–Baleanu–Caputo (ABC) derivatives are

$$^{CF}D_t^\alpha f(t) = \frac{B(\alpha)(2-\alpha)}{2(1-\alpha)}\int_{t_0}^t f'(x)\exp\Big[-\frac{\alpha}{1-\alpha}(t-x)\Big]dx,$$

$$^{ABC}_{t_0}D_t^\alpha f(t) = \frac{B(\alpha)}{1-\alpha}\int_{t_0}^t f'(x)E_\alpha\Big[-\frac{\alpha}{1-\alpha}(t-x)^\alpha\Big]dx,$$

where $E_\alpha(z) = \sum_{j\ge0} z^j/\Gamma(\alpha j + 1)$ is the Mittag-Leffler function. Both have non-singular kernels.

**Theorem (generalized Volterra estimate).** Let $g$ be nonnegative, differentiable and strictly increasing on $\mathbb R_+$, let $u^* > 0$, and set

$$\Psi(u) = \int_{u^*}^u \frac{g(s) - g(u^*)}{g(s)}\,ds = u - u^* - \int_{u^*}^u \frac{g(u^*)}{g(s)}\,ds \ \ (\ge 0,\ \text{with equality only at } u = u^*).$$

For every positive differentiable function $u$, every $t \ge t_0$ and $0 < \alpha < 1$,

$$^{ABC}_{t_0}D_t^\alpha \Psi(u(t)) \le \Big(1 - \frac{g(u^*)}{g(u(t))}\Big)\, {}^{ABC}_{t_0}D_t^\alpha u(t), \qquad {}^{CF}D_t^\alpha \Psi(u(t)) \le \Big(1 - \frac{g(u^*)}{g(u(t))}\Big)\, {}^{CF}D_t^\alpha u(t).$$

With $g(u) = u$ this is the fractional analogue of the classical Volterra bound for $u - u^* - u^*\ln(u/u^*)$.

**Application (fractional SEIR with general incidence).** Consider

$$D^\alpha S = \Lambda^\alpha - d^\alpha S - F(S,I),\quad D^\alpha E = F(S,I) - m_1 E,\quad D^\alpha I = \sigma^\alpha E - m_2 I,$$

with $D^\alpha$ any of the Caputo, CF or ABC derivatives, $m_1 = \sigma^\alpha + d^\alpha$, $m_2 = \gamma^\alpha + d^\alpha$, and $F(S,I) = I F_1(S,I)$ with $\partial_S F_1 > 0$, $\partial_I F_1 \le 0$, $\partial_I F \ge 0$, $F(S,0) = F(0,I) = 0$. With $S_0 = \Lambda^\alpha/d^\alpha$ and

$$R_0 = \frac{\sigma^\alpha}{m_1m_2}\frac{\partial F}{\partial I}(S_0, 0),$$

the disease-free equilibrium is asymptotically stable when $R_0 \le 1$, and the endemic equilibrium is asymptotically stable when $R_0 > 1$.

## Proof depends on

- [Generalized Volterra estimate for Caputo derivatives](../../../systems-biology/cellular-and-biochemical-dynamics/lyapunov-functions-for-caputo-fractional-biological-models/generalized-volterra-estimate-for-caputo-derivatives.md)

## Proof sketch

The proof writes $\Psi(u(t))$ through its derivative $1 - g(u^*)/g(u)$, integrates by parts against the kernel (exponential for CF, Mittag-Leffler for ABC), and uses that the kernel is positive and decreasing while $\Psi$ is convex in the appropriate sense, so the remainder term has a sign. The inequality lets one differentiate Lyapunov functions such as $V = \Psi_1(S) + E - E^* - E^*\ln(E/E^*) + c\,(I - I^* - I^*\ln(I/I^*))$ along fractional dynamics exactly as in the integer-order case; choosing $g(S) = F(S, I^*)$ handles non-separable incidences, which the plain Volterra estimate cannot.

## Sources

- Adnane Boukhouima, Houssine Zine, El Mehdi Lotfi, Marouane Mahrouf, Delfim F.M. Torres and Noura Yousfi, "Lyapunov functions and stability analysis of fractional-order systems", in *Mathematical Analysis of Infectious Diseases*, Elsevier, 2022, 125–136, <https://doi.org/10.1016/b978-0-32-390504-6.00013-9>. Preprint version: arXiv:2202.00603 (2022), Definitions 2.3–2.4, Theorem 3.1, Corollary 3.4 (Section 3) and Theorem 4.1 (Section 4), <https://doi.org/10.48550/arXiv.2202.00603>.
