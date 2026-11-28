# Double robustness, regression branch

Let $(\Omega, \mu)$ be a probability space, $\mathcal{X}$ a finite set with measurable singletons, $X : \Omega \to \mathcal{X}$ a measurable covariate, $R \subseteq \Omega$ a measurable response event, and $Y : \Omega \to \mathbb{R}$ a measurable integrable outcome. Write $e(x) = \mu(R \cap \{X = x\}) / \mu(X = x)$ for the response propensity and $m_Y(x) = \int_{\{X = x\}} Y \, d\mu / \mu(X = x)$ for the outcome regression (both $0$ when $\mu(X = x) = 0$). Assume missing at random: for every Borel $B \subseteq \mathbb{R}$ and every $x$,

$$\mu(R \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(R \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$

For $\pi, m : \mathcal{X} \to \mathbb{R}$ let $\psi = m(X) + \mathbf{1}_R (Y - m(X))/\pi(X)$ be the AIPW score, with $a / 0 = 0$. If the outcome regression is correct, $m(x) = m_Y(x)$ for every $x$ with $\mu(X = x) > 0$, then for every response propensity $\pi$ (including values $\pi(x) = 0$),

$$\mathbb{E}\Bigl[m(X) + \mathbf{1}_R \, \frac{Y - m(X)}{\pi(X)}\Bigr] = \mathbb{E}[Y].$$

Positivity of the response is not needed for this identity.
