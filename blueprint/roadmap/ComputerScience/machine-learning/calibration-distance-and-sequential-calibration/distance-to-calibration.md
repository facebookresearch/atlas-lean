# Distance to calibration and its upper and lower variants

Let $D$ be a distribution over $X \times \{0,1\}$ and $f : X \to [0,1]$ a predictor; let $\mathrm{cal}(D)$ be the set of perfectly calibrated predictors $g$ (those with $\mathbb{E}[y \mid g(x)] = g(x)$ almost surely). The **true distance to calibration** is $\mathrm{dCE}_D(f) = \inf_{g \in \mathrm{cal}(D)} \mathbb{E}_D|f(x) - g(x)|$. In the **prediction-only access model**, where only the joint law $\Gamma$ of $(f(x), y)$ is available, one defines the **upper distance** $\overline{\mathrm{dCE}}(\Gamma) = \inf_{\kappa} \mathbb{E}_{(v,y) \sim \Gamma}|v - \kappa(v)|$ over post-processings $\kappa : [0,1] \to [0,1]$ making $(\kappa(v), y)$ perfectly calibrated, and the **lower distance** $\underline{\mathrm{dCE}}(\Gamma) = \inf_\Pi \mathbb{E}_\Pi|u - v|$ over couplings $\Pi$ of $(u, v, y)$ with $(v,y) \sim \Gamma$ and $(u, y)$ perfectly calibrated. The lower and upper distances are respectively the infimum and the supremum of $\mathrm{dCE}_D(f)$ over all $(D, f)$ inducing $\Gamma$. The **expected calibration error** is $\mathrm{ECE}_D(f) = \mathbb{E}\,\big|\mathbb{E}[y \mid f(x)] - f(x)\big|$.

## Sources

- J. Blasiok, P. Gopalan, L. Hu, P. Nakkiran, "A Unifying Theory of Distance from Calibration", STOC (2023), arXiv:2211.16886.
