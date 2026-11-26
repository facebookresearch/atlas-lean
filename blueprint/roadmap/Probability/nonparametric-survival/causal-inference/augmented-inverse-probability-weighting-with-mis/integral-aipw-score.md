# Double robustness of the AIPW score with missing outcomes

Let $(\Omega, \mu)$ be a probability space, $\mathcal{X}$ a finite set with measurable singletons, $X : \Omega \to \mathcal{X}$ a measurable covariate, $R \subseteq \Omega$ a measurable response event, and $Y : \Omega \to \mathbb{R}$ a measurable integrable outcome. Write $e(x) = \mu(R \cap \{X = x\}) / \mu(X = x)$ for the response propensity and $m_Y(x) = \int_{\{X = x\}} Y \, d\mu / \mu(X = x)$ for the outcome regression (both $0$ when $\mu(X = x) = 0$). Assume missing at random: for every Borel $B \subseteq \mathbb{R}$ and every $x$,

$$\mu(R \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(R \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$

For $\pi, m : \mathcal{X} \to \mathbb{R}$ let $\psi = m(X) + \mathbf{1}_R (Y - m(X))/\pi(X)$ be the AIPW score, with $a / 0 = 0$. Assume also positivity of the response: there is $\varepsilon > 0$ with $e(x) \ge \varepsilon$ for every $x$ with $\mu(X = x) > 0$. If either the response propensity is correct, $\pi(x) = e(x)$ for every $x$ with $\mu(X = x) > 0$, or the outcome regression is correct, $m(x) = m_Y(x)$ for every $x$ with $\mu(X = x) > 0$, then

$$\mathbb{E}\Bigl[m(X) + \mathbf{1}_R \, \frac{Y - m(X)}{\pi(X)}\Bigr] = \mathbb{E}[Y].$$

The nuisances $\pi$ and $m$ are fixed functions of the covariate value (Robins, Rotnitzky and Zhao 1994; Bang and Robins 2005).
