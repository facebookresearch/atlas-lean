# Three classes of travelling waves in the mutant–immune cell model

After reduction to a slow invariant manifold, the densities of mutant epithelial cells $M(x,t)$ and immune cells $I(x,t)$, both in $[0,1]$, obey

$$

M_t = M_{xx} + I M (1-M), \qquad I_t = D I_{xx} + \delta^{-1} f(M,I),

$$

$$

f(M,I) = \frac{a(\sigma)\, I\,\big(b(\sigma)(\sigma-1) + b(\sigma) M - I\big)}{\alpha_2 I + \beta_2 (1-M)}, \qquad a(\sigma) = \beta_1(\beta_2\sigma + \alpha_2), \quad b(\sigma) = \frac{\beta_2}{\beta_2\sigma + \alpha_2},

$$

with $\delta \ll 1$ (slow mutant growth relative to immune response) and $\sigma > 0$ a ratio of growth to decay rates of the non-mutant components. A **full-transition permanent form travelling wave** (FPTW) is a nonnegative solution depending on $z = x - vt$ with $v > 0$ that connects the fully mutant inflamed state as $z \to -\infty$ to $(0,0)$ as $z \to +\infty$. As $\delta \to 0$ the immune density is slaved, $I \approx b(\sigma)\,(M-(1-\sigma))_+$, and $M$ solves

$$

\tilde M'' + v \tilde M' + F(\tilde M) = 0, \qquad F(X) = H_0(X)\,X(1-X), \quad H_0(X) = b(\sigma)\,(X-(1-\sigma))_+ .

$$

**Theorem.** For $\delta$ sufficiently small:

1. (Bistable reaction with cut-off, $\delta \le \sigma < 1$.) There is a unique FPTW, with speed $v \sim v^*(\sigma)$, where $v^*(\sigma)$ is the unique speed for which the reduced problem with $\tilde M(0) = 1-\sigma$ has a monotone solution. The function $v^*$ is continuous and increasing on $(0,1)$, with $v^*(\sigma) = O(\sigma^{3/2})$ as $\sigma \to 0^+$ and $v^*(\sigma) \to \sqrt{b(1)/2}$ as $\sigma \to 1^-$, and $\tilde M(z) = (1-\sigma)e^{-v^*(\sigma) z}$ for $z \ge 0$.
2. (Cubic Fisher reaction, $\sigma = 1$.) Here $F(X) = b(1)X^2(1-X)$. There is a unique (up to translation) FPTW for each speed $v \ge v_m(\delta)$ with $v_m(\delta) \sim \sqrt{b(1)/2}$, and none for $0 \le v < v_m(\delta)$. At the minimal speed the leading-order profile is $\tilde M(z) = e^{-v^* z}/(1+e^{-v^* z})$ with $v^* = \sqrt{b(1)/2}$, while for $v > v^*$ the profile decays algebraically, $\tilde M(z) \sim v/(b(1) z)$ as $z \to \infty$.
3. (KPP reaction, $\sigma > 1$.) There are no FPTWs; the propagation is carried by upper- and lower-transition travelling waves governed by a KPP (Fisher) nonlinearity.

The mutant cells thus decide which class of front occurs, while the leading-order speed is set by the immune and barrier dynamics.

## Expansion

The fast–slow structure ($\delta \to 0$) puts $I$ on the attracting branch of $f(M,I) = 0$, namely $I = 0$ for $M \le 1-\sigma$ and $I = b(\sigma)(M-1+\sigma)$ above it. Substituting gives the scalar equation for $M$. For $\sigma < 1$ the reaction vanishes on $[0,1-\sigma]$ and is positive above, a cut-off problem with a unique speed; for $z \ge 0$ the equation is $\tilde M'' + v\tilde M' = 0$, giving the explicit exponential tail. At $\sigma = 1$ the cut-off disappears and the degenerate Fisher term $X^2(1-X)$ gives a half-line of speeds whose minimal wave is explicit. Matched asymptotic expansions then lift the reduced waves to waves of the full system.

## Sources

- Blaine van Rensburg, David J. Needham, Fabian Spill, Alexandra Tzella, "The role of mutants in the spatio-temporal progression of inflammatory bowel disease: three classes of permanent form travelling waves", arXiv (2025). Section 2 and Section 4 (Definitions 4.1–4.3, Theorems 4.1–4.4 and 4.9). <https://doi.org/10.48550/arXiv.2501.07205>. Published version: SIAM Journal on Applied Dynamical Systems 25(2) (2026), 902–939, <https://doi.org/10.1137/25m1781760>; locators above refer to the arXiv version.
