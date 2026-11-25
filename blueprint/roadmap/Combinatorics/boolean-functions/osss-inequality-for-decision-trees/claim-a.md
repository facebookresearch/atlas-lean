# Root step of the OSSS induction

Let $E$ be a finite set, $\nu$ a [product probability weight](is-prob-weight.md) on $\{0, 1\}^E$, $e \in E$, and $F, g : \{0, 1\}^E \to \mathbb{R}$ with $\lvert F(\omega^{e \to 1}) - F(\omega^{e \to 0})\rvert \le 1$ for every $\omega$. Then

$$\mathrm{Cov}_\nu\big(F,\ g - \mathbb{E}_\nu[g \mid \omega_{\ne e}]\big) \le \mathrm{Inf}_e(g),$$

where $\mathbb{E}_\nu[g \mid \omega_{\ne e}](\omega) = \nu_e(1)\, g(\omega^{e \to 1}) + \nu_e(0)\, g(\omega^{e \to 0})$ is the [conditional expectation](cond-mean.md) given the other coordinates and $\mathrm{Inf}_e(g) = \mathbb{E}_\nu\lvert g(\omega^{e \to 1}) - g(\omega^{e \to 0})\rvert$ the [influence](infl.md). This is the root step of the induction proving the OSSS inequality.
