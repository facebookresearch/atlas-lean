# Set Integral inter eq propensity mul

Let $\mu$ be a finite measure on $\Omega$, $\mathcal X$ a type, $T \subseteq \Omega$, $X : \Omega \to \mathcal X$ and $Y : \Omega \to \mathbb R$ measurable. Suppose $T$ is conditionally independent of $Y$ given $X$ in the discrete sense: for every measurable $B \subseteq \mathbb R$ and every $x$,

$$\mu(T \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(T \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$

Then for every $x \in \mathcal X$,

$$\int_{T \cap \{X = x\}} Y \, d\mu = e(x) \int_{\{X = x\}} Y \, d\mu,$$

where the propensity is $e(x) = \mu(T \cap \{X = x\}) / \mu(X = x)$, taken to be $0$ when $\mu(X = x) = 0$. No integrability of $Y$ is assumed (non-integrable integrals take the value $0$).
