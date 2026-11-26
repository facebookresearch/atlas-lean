# Likelihood factorization under missing at random

Let $Y$ be a measurable space carrying the counting measure, and let $(f_\theta)_{\theta \in \Theta}$ be a family of densities with respect to it: a.e. measurable $f_\theta : Y \to [0, \infty]$ with $\int f_\theta \, d\#= 1$. For $\psi \in \Psi$ and $y \in Y$ let $g_\psi(\cdot \mid y)$ be a probability mass function on the set $M$ of missingness patterns, and let $o(y, m)$ be the observed part of $y$ under pattern $m$. Fix a realized observation $(y_0, m_0)$, put $C = \{y \in Y : o(y, m_0) = o(y_0, m_0)\}$, and let $S \subseteq \Theta \times \Psi$ be the parameter set with projections $S_\Theta$ and $S_\Psi$. Assume

- realized missing at random: $g_\psi(m_0 \mid y) = g_\psi(m_0 \mid y')$ for every $\psi$ in the second projection $S_\Psi$ and all $y, y' \in C$;
- variation independence: $S = S_\Theta \times S_\Psi$.

Then for all $\theta \in \Theta$ and $\psi \in \Psi$, with sums of $[0, \infty]$-valued terms over $y \in C$,

$$\mathbf{1}_S(\theta, \psi) \sum_{y \in C} f_\theta(y)\, g_\psi(m_0 \mid y) = \mathbf{1}_{S_\Psi}(\psi)\, g_\psi(m_0 \mid y_0) \cdot \mathbf{1}_{S_\Theta}(\theta) \sum_{y \in C} f_\theta(y).$$

The outcome space need not be countable, and no measurability of singletons is needed.

## Sources

- S. Seaman, J. Galati, D. Jackson and J. Carlin, "What is meant by 'missing at random'?", Statistical Science 28 (2013), Theorem 1(i).
