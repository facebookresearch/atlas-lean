# Aipw Score bias gateaux zero

Let $(\Omega, \mu)$ be a probability space, $\mathcal{X}$ a finite set with measurable singletons, $X : \Omega \to \mathcal{X}$ a measurable covariate, $R \subseteq \Omega$ a measurable response event, and $Y : \Omega \to \mathbb{R}$ a measurable integrable outcome. Write $e(x) = \mu(R \cap \{X = x\}) / \mu(X = x)$ for the response propensity and $m_Y(x) = \int_{\{X = x\}} Y \, d\mu / \mu(X = x)$ for the outcome regression (both $0$ when $\mu(X = x) = 0$). Assume missing at random: for every Borel $B \subseteq \mathbb{R}$ and every $x$,

$$\mu(R \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(R \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$

For $\pi, m : \mathcal{X} \to \mathbb{R}$ let $\psi = m(X) + \mathbf{1}_R (Y - m(X))/\pi(X)$ be the AIPW score, with $a / 0 = 0$. Assume also positivity of the response: there is $\varepsilon > 0$ with $e(x) \ge \varepsilon$ for every $x$ with $\mu(X = x) > 0$. For fixed directions $\delta_m, \delta_e : \mathcal{X} \to \mathbb{R}$, perturb the nuisances away from the true ones, $\pi_t = e + t\,\delta_e$ and $m_t = m_Y + t\,\delta_m$, and let

$$b(t) = \mathbb{E}\Bigl[m_t(X) + \mathbf{1}_R \, \frac{Y - m_t(X)}{\pi_t(X)}\Bigr] - \mathbb{E}[Y], \qquad t \in \mathbb{R},$$

be the bias of the AIPW score. Then $b$ is differentiable at $t = 0$ with $b'(0) = 0$: the AIPW bias has zero Gateaux derivative at the true nuisances in every direction (Neyman orthogonality).
