# Double robustness of the AIPW score for the average treatment effect

Let $(\Omega, \mu)$ be a probability space, $\mathcal{X}$ a finite set with measurable singletons, $X : \Omega \to \mathcal{X}$ a measurable covariate, $T \subseteq \Omega$ a measurable treatment event, and $Y_0, Y_1 : \Omega \to \mathbb{R}$ measurable integrable potential outcomes. Write $e^*(x) = \mu(T \cap \{X = x\}) / \mu(X = x)$ and $m_a(x) = \int_{\{X = x\}} Y_a \, d\mu / \mu(X = x)$. Assume strong ignorability of $T$ given $X$ for the pair $(Y_0, Y_1)$:

- for every Borel $B \subseteq \mathbb{R}^2$ and every $x$, $\mu(T \cap \{(Y_0, Y_1) \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(T \cap \{X = x\})\, \mu(\{(Y_0, Y_1) \in B\} \cap \{X = x\})$;
- overlap: $0 < e^*(x) < 1$ for every $x$ with $\mu(X = x) > 0$.

Let $e, g_0, g_1 : \mathcal{X} \to \mathbb{R}$, and suppose that either $e(x) = e^*(x)$ for every $x$ with $\mu(X = x) > 0$, or both $g_0(x) = m_0(x)$ and $g_1(x) = m_1(x)$ for every such $x$. With the observed outcome $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$ and the convention $a / 0 = 0$,

$$\mathbb{E}\Bigl[g_1(X) + \mathbf{1}_T \, \frac{Y - g_1(X)}{e(X)} - g_0(X) - \mathbf{1}_{T^c} \, \frac{Y - g_0(X)}{1 - e(X)}\Bigr] = \mathbb{E}[Y_1 - Y_0].$$
