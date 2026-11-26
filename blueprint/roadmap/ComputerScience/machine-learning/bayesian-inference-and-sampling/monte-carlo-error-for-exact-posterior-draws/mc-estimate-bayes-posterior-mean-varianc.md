# Monte Carlo with exact posterior draws: mean and variance

Let $\Theta$ and $\mathcal{X}$ be measurable spaces, with measurable singletons in $\mathcal{X}$, let $\kappa$ be a Markov kernel from $\Theta$ to $\mathcal{X}$ (the likelihood), $\pi$ a finite prior measure on $\Theta$ and $x \in \mathcal{X}$ an observation with positive evidence $(\kappa \circ \pi)(\{x\}) \ne 0$. Let $\Pi_x$ be the Bayes posterior. Let $g : \Theta \to \mathbb{R}$ be measurable with $g \in L^2(\Pi_x)$, and let $\theta_0, \theta_1, \ldots : \Omega \to \Theta$ be measurable, mutually independent under a measure $\mu$, each with law $\Pi_x$. Then for every $m \ne 0$ the Monte Carlo average $\widehat{g}_m = \frac{1}{m}\sum_{i<m} g(\theta_i)$ satisfies

$$\int \widehat{g}_m \, d\mu = \int g \, d\Pi_x \qquad\text{and}\qquad \operatorname{Var}_\mu(\widehat{g}_m) = \frac{\operatorname{Var}_{\Pi_x}(g)}{m} .$$
