# Observed-data density under copula-dependent censoring

Let $T, C \ge 0$ be a survival and a censoring time with continuous marginal distribution functions $F_T, F_C$ and marginal densities $f_T, f_C$, and observe $Y = \min(T, C)$ and $\Delta = \mathbf 1\{T \le C\}$. By Sklar's theorem there is a unique copula $\mathcal C$ with $F_{T,C}(t, c) = \mathcal C(F_T(t), F_C(c))$. Continuous margins alone do not exclude ties: if $T = C$ is uniform, both margins have densities but $\Delta = 1$ always, and the copula $\min(u, v)$ is not differentiable on the diagonal. Assume therefore that $(T, C)$ has a joint density (so $P(T = C) = 0$) and that $\mathcal C$ has continuous first partial derivatives on $(0, 1)^2$. Put

$$h_{C|T}(v \mid u) = \frac{\partial}{\partial u}\mathcal C(u, v), \qquad h_{T|C}(u \mid v) = \frac{\partial}{\partial v}\mathcal C(u, v),$$

so that $F_{C|T}(c \mid t) = h_{C|T}(F_C(c) \mid F_T(t))$. Then

$$F_Y(y) = F_T(y) + F_C(y) - \mathcal C(F_T(y), F_C(y)),$$

$$f_{Y,\Delta}(y, 1) = \bigl\{1 - h_{C|T}(F_C(y) \mid F_T(y))\bigr\} f_T(y), \qquad f_{Y,\Delta}(y, 0) = \bigl\{1 - h_{T|C}(F_T(y) \mid F_C(y))\bigr\} f_C(y).$$

For an Archimedean copula $\mathcal C(u, v) = \psi^{[-1]}(\psi(u) + \psi(v))$, at points with $\psi(u) + \psi(v) < \psi(0)$ where $\psi$ is differentiable at $u$ and at $\mathcal C(u, v)$ with $\psi'(\mathcal C(u, v)) \ne 0$, $h_{C|T}(v \mid u) = \psi'(u)/\psi'(\psi^{-1}(\psi(u) + \psi(v)))$, and symmetrically for $h_{T|C}$; where these derivatives do not exist the formula does not apply. Under independence ($\mathcal C(u,v) = uv$) the formulas reduce to the classical $f_T(y)\{1 - F_C(y)\}$ and $f_C(y)\{1 - F_T(y)\}$.

## Expansion

$P(Y > y) = P(T > y, C > y) = 1 - F_T(y) - F_C(y) + \mathcal C(F_T(y), F_C(y))$. For $\Delta = 1$, $P(Y \le y, \Delta = 1) = \int_0^y P(C \ge t \mid T = t) f_T(t)\,dt$. Because the joint law has a density, $P(C = t \mid T = t) = 0$ for almost every $t$, so $P(C \ge t \mid T = t) = P(C > t \mid T = t) = 1 - P(C \le t \mid T = t)$, and $P(C \le c \mid T = t) = \partial_u \mathcal C(u, F_C(c))|_{u = F_T(t)}$ for almost every $t$ by the differentiability of $\mathcal C$; differentiate in $y$. The case $\Delta = 0$ is symmetric. The Archimedean formula is the chain rule applied to $\psi(\mathcal C(u, v)) = \psi(u) + \psi(v)$.

## Sources

- C. Czado and I. Van Keilegom, "Dependent censoring based on parametric copulas", *Biometrika* (published online 2022), <https://doi.org/10.1093/biomet/asac067>. Model (2.1)–(2.3), equation (2.4) and its derivation in the Appendix, equation (3.1) and the Archimedean conditional distribution functions.
