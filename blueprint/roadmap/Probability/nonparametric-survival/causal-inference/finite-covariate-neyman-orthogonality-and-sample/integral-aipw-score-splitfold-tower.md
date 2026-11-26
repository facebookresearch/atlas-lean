# Integral aipw Score splitfold tower

Let $(\Omega, \mu)$ be a probability space, $\mathcal{X}$ a finite set with measurable singletons, $X : \Omega \to \mathcal{X}$ a measurable covariate, $R \subseteq \Omega$ a measurable response event, and $Y : \Omega \to \mathbb{R}$ a measurable integrable outcome. Write $e(x) = \mu(R \cap \{X = x\}) / \mu(X = x)$ for the response propensity and $m_Y(x) = \int_{\{X = x\}} Y \, d\mu / \mu(X = x)$ for the outcome regression (both $0$ when $\mu(X = x) = 0$). Assume missing at random: for every Borel $B \subseteq \mathbb{R}$ and every $x$,

$$\mu(R \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(R \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$

For $\pi, m : \mathcal{X} \to \mathbb{R}$ let $\psi = m(X) + \mathbf{1}_R (Y - m(X))/\pi(X)$ be the AIPW score, with $a / 0 = 0$. Let $(\Omega_t, \mu_t)$ be a probability space of training samples, and let $\hat m, \hat\pi : \Omega_t \to (\mathcal{X} \to \mathbb{R})$ be fitted nuisances depending on the training sample only. Write $\psi_{\omega_t}(\omega) = \hat m(\omega_t)(X(\omega)) + \mathbf{1}_R(\omega)\, \bigl(Y(\omega) - \hat m(\omega_t)(X(\omega))\bigr)/\hat\pi(\omega_t)(X(\omega))$, and assume $(\omega_t, \omega) \mapsto \psi_{\omega_t}(\omega)$ is integrable for the product law $\mu_t \otimes \mu$ (independent training and evaluation folds). Then

$$\int \psi_{\omega_t}(\omega)\, d(\mu_t \otimes \mu) = \mathbb{E}[Y] + \int_{\Omega_t} \sum_{x \in \mathcal{X}} \left(\frac{e(x)}{\hat\pi(\omega_t)(x)} - 1\right)\left(\int_{\{X = x\}} Y \, d\mu - \hat m(\omega_t)(x)\, \mu(X = x)\right) d\mu_t(\omega_t).$$

The joint bias over training and evaluation is the training mean of the stratumwise product-bias sums.
