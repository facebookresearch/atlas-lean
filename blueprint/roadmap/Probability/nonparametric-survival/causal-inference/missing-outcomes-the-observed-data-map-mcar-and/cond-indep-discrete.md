# Missing completely at random implies discrete conditional independence

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$, $X : \Omega \to \mathcal X$ with $\mathcal X$ a measurable space with measurable singletons, and $Y : \Omega \to \mathcal Y$ with $\mathcal Y$ a measurable space. If the outcome is missing completely at random ($\mathbf 1_R$ independent of $(X, Y)$ under $\mu$), then $R$ is conditionally independent of $Y$ given $X$ in the discrete sense: for every measurable $B \subseteq \mathcal Y$ and every $x \in \mathcal X$,

$$\mu_{\mathbb R}(R \cap \{Y \in B\} \cap \{X = x\})\, \mu_{\mathbb R}(X = x) = \mu_{\mathbb R}(R \cap \{X = x\})\, \mu_{\mathbb R}(\{Y \in B\} \cap \{X = x\}),$$

where $\mu_{\mathbb R}(A)$ is the real number $\mu(A)$ when $\mu(A) < \infty$ and $0$ when $\mu(A) = \infty$.
