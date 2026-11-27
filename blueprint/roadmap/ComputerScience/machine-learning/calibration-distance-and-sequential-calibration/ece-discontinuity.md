# The expected calibration error is discontinuous and not robustly complete

Let $X = \{0, 1\}$ with the uniform distribution and $y = x$ deterministically, and for $0 < \varepsilon < \tfrac12$ let $f_\varepsilon(0) = \tfrac12 - \varepsilon$, $f_\varepsilon(1) = \tfrac12 + \varepsilon$. The constant predictor $\tfrac12$ is perfectly calibrated, so $\mathrm{dCE}(f_\varepsilon) \le \varepsilon$, whereas $\mathrm{ECE}(f_\varepsilon) = \tfrac12 - \varepsilon$. Hence $\mathrm{ECE}$ jumps from $\mathrm{ECE}(f_0) = 0$ to nearly $\tfrac12$ under arbitrarily small perturbations of the predictor and satisfies no bound of the form $\mathrm{ECE} \le a\, \mathrm{dCE}^c$ for any $c > 0$. In the other direction $\mathrm{ECE}_D(f) \ge \mathrm{dCE}_D(f)$ always, since replacing $f$ by $x \mapsto \mathbb{E}[y \mid f(x)]$ is a perfectly calibrated predictor at $\ell_1$ distance $\mathrm{ECE}_D(f)$.

## Proof sketch

For $f_\varepsilon$ the level sets are singletons with outcomes $0$ and $1$, so $|\mathbb{E}[y \mid f] - f| = \tfrac12 - \varepsilon$ on both. The general inequality uses $g(x) = \mathbb{E}[y \mid f(x)]$, which is calibrated because $\mathbb{E}[y \mid g(x)] = g(x)$ by the tower property, and $\mathbb{E}|f - g| = \mathrm{ECE}(f)$.

## Depends on

- [Distance to calibration and its upper and lower variants](distance-to-calibration.md)

## Sources

- J. Blasiok, P. Gopalan, L. Hu, P. Nakkiran, "A Unifying Theory of Distance from Calibration", STOC (2023), arXiv:2211.16886, Lemmas 4.7 and 4.8.
