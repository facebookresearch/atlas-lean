# Truncated-Gaussian pivot for testing a selected changepoint

Let $Y = \theta + \varepsilon$ with $\theta \in \mathbb{R}^n$ unknown and $\varepsilon \sim \mathcal{N}_n(0, \sigma^2 I_n)$, $\sigma^2$ known (the **saturated model**). Let $y_{\mathrm{obs}}$ be the observed data, and suppose a changepoint algorithm selects a model $M(y_{\mathrm{obs}})$ whose selection event is polyhedral, $\{y : M(y) = M(y_{\mathrm{obs}})\} = \{y : \Gamma y \ge 0\}$ up to a Lebesgue-null set, for a matrix $\Gamma$ determined by $M(y_{\mathrm{obs}})$. This holds for $k$-step [binary segmentation](polyhedral-selection-event-of-binary-segmentation.md) with $M$ the ordered changepoints and directions; for wild binary segmentation it holds only when $M$ also records the sampled intervals and the winning interval at each step (Hyun et al. 2021, §3.1.2, Proposition 2), and the theorem below then conditions on that larger record. Let $v \in \mathbb{R}^n \setminus \{0\}$ be a contrast chosen as a function of $M(y_{\mathrm{obs}})$ only, typically the difference of segment means on either side of a selected changepoint, and let $\Pi_v^{\perp}$ be the orthogonal projection onto $v^{\perp}$.

Put $\rho = \Gamma v / \|v\|_2^2$, $\tau = \sigma \|v\|_2$, and

$$\mathcal{V}^{\mathrm{lo}} = v^{\top} y_{\mathrm{obs}} - \min_{j : \rho_j > 0} \frac{(\Gamma y_{\mathrm{obs}})_j}{\rho_j}, \qquad \mathcal{V}^{\mathrm{up}} = v^{\top} y_{\mathrm{obs}} - \max_{j : \rho_j < 0} \frac{(\Gamma y_{\mathrm{obs}})_j}{\rho_j},$$

with the conventions $\min \emptyset = +\infty$, $\max \emptyset = -\infty$.

**Theorem (polyhedral lemma; Lee et al. 2016, Tibshirani et al. 2016, as used by Hyun et al. 2021, Eqs. 5, 8 and 9 of the published edition).** Conditional on $M(Y) = M(y_{\mathrm{obs}})$ and $\Pi_v^{\perp} Y = \Pi_v^{\perp} y_{\mathrm{obs}}$, the statistic $v^{\top} Y$ is distributed as $\mathcal{N}(v^{\top}\theta, \tau^2)$ truncated to $[\mathcal{V}^{\mathrm{lo}}, \mathcal{V}^{\mathrm{up}}]$. Hence under $H_0 : v^{\top}\theta = 0$,

$$p(y_{\mathrm{obs}}) = \frac{\Phi(\mathcal{V}^{\mathrm{up}}/\tau) - \Phi(v^{\top} y_{\mathrm{obs}}/\tau)}{\Phi(\mathcal{V}^{\mathrm{up}}/\tau) - \Phi(\mathcal{V}^{\mathrm{lo}}/\tau)}$$

is an exact one-sided selective $p$-value against $H_1 : v^{\top}\theta > 0$: it is uniform on $[0, 1]$ under $H_0$ conditional on the selection event, so the test controls type I error at every level after data-driven changepoint selection.

## Depends on

- [Binary segmentation selects a polyhedral cone of data vectors](polyhedral-selection-event-of-binary-segmentation.md)

## Expansion

Decompose $y = \Pi_v^{\perp} y + (v^{\top} y)\, v / \|v\|_2^2$. Then $\Gamma y = \Gamma \Pi_v^{\perp} y + \rho\, (v^{\top} y) \ge 0$. Holding $z = \Pi_v^{\perp} y = \Pi_v^{\perp} y_{\mathrm{obs}}$ fixed, each row with $\rho_j > 0$ gives a lower bound and each row with $\rho_j < 0$ an upper bound on $v^{\top} y$; using $(\Gamma z)_j = (\Gamma y_{\mathrm{obs}})_j - \rho_j v^{\top} y_{\mathrm{obs}}$ these bounds are exactly $\mathcal{V}^{\mathrm{lo}}$ and $\mathcal{V}^{\mathrm{up}}$ (rows with $\rho_j = 0$ do not involve $v^{\top} y$). The null set by which the selection event may differ from the cone has conditional probability zero, so it does not change the conditional law. For Gaussian $Y$, $v^{\top} Y$ is independent of $\Pi_v^{\perp} Y$, so conditioning only truncates its $\mathcal{N}(v^{\top}\theta, \tau^2)$ law. The probability integral transform of a truncated normal is uniform, which yields the pivot.

## Sources

- S. Hyun, K. Z. Lin, M. G'Sell and R. J. Tibshirani, "Post-selection inference for changepoint detection algorithms with application to copy number variation data", Biometrics 77 (2021), 1037–1049, <https://doi.org/10.1111/biom.13422>. Numbering of the published journal edition: Section 2.1.1 (CUSUM statistic, Eq. 3), Section 2.2.1 (saturated-model selective distribution, Eq. 5), Section 3.1.2 (Proposition 2, the wild binary segmentation record) and Section 3.2.1 (truncated-Gaussian pivot and truncation limits, Eqs. 8–9).
- J. D. Lee, D. L. Sun, Y. Sun and J. E. Taylor, "Exact post-selection inference, with application to the lasso", Annals of Statistics 44 (2016), 907–927, <https://doi.org/10.1214/15-AOS1371>.
