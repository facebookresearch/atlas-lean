# Exact bias of the AIPW score under MAR

Let $(\Omega, \mu)$ be a probability space, $\mathcal{X}$ a finite set with measurable singletons, $X : \Omega \to \mathcal{X}$ a measurable covariate, $R \subseteq \Omega$ a measurable response event, and $Y : \Omega \to \mathbb{R}$ a measurable integrable outcome. Write $e(x) = \mu(R \cap \{X = x\}) / \mu(X = x)$ for the response propensity and $m_Y(x) = \int_{\{X = x\}} Y \, d\mu / \mu(X = x)$ for the outcome regression (both $0$ when $\mu(X = x) = 0$). Assume missing at random: for every Borel $B \subseteq \mathbb{R}$ and every $x$,

$$\mu(R \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(R \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$

For $\pi, m : \mathcal{X} \to \mathbb{R}$ let $\psi = m(X) + \mathbf{1}_R (Y - m(X))/\pi(X)$ be the AIPW score, with $a / 0 = 0$. Then, for all $\pi$ and $m$, $\psi$ is integrable and

$$\mathbb{E}[\psi] = \mathbb{E}[Y] + \sum_{x \in \mathcal{X}} \left(\frac{e(x)}{\pi(x)} - 1\right) \left(\int_{\{X = x\}} Y \, d\mu - m(x)\, \mu(X = x)\right).$$

Each term is the product of the response-propensity error and the regression error on the stratum $\{X = x\}$. No positivity or condition on $\pi, m$ is assumed; where $\pi(x) = 0$ the factor $e(x)/\pi(x) - 1$ equals $-1$.
