# Likelihood comparisons agree under realized MAR

Let $Y$ be a measurable space of full-data values with measurable singletons, carrying the counting measure, and let $(f_\theta)_{\theta \in \Theta}$ be a family of a.e. measurable $[0,\infty]$-valued densities on $Y$ with $\sum_{y} f_\theta(y) = 1$ for every $\theta$. The outcome space need not be countable. For $\psi \in \Psi$ and $y \in Y$ let $g_\psi(\cdot \mid y)$ be a probability mass function on the set $M$ of response patterns, and let $o(y, m)$ be the observed part of $y$ under pattern $m$. Fix realized values $y_0 \in Y$, $m_0 \in M$, put $C = \{y \in Y : o(y, m_0) = o(y_0, m_0)\}$, and let $S \subseteq \Theta \times \Psi$ be the parameter space with projections $S_\Theta$ and $S_\Psi$. Assume

- realized missing at random: $g_\psi(m_0 \mid y) = g_\psi(m_0 \mid y')$ for every $\psi \in S_\Psi$ and all $y, y' \in C$;
- variation independence: $S = S_\Theta \times S_\Psi$.

Define, with values in $[0,\infty]$, the observed-data likelihood extended by zero outside $S$ and the full-data likelihood of the observed data,

$$L_1(\theta, \psi) = \mathbf{1}_S(\theta, \psi) \sum_{y \in C} f_\theta(y)\, g_\psi(m_0 \mid y), \qquad L_2(\theta) = \sum_{y \in C} f_\theta(y).$$

Let $\psi \in S_\Psi$ with $g_\psi(m_0 \mid y_0) \neq 0$, and let $\theta_1, \theta_2 \in S_\Theta$. Then

$$L_1(\theta_1, \psi) \le L_1(\theta_2, \psi) \iff L_2(\theta_1) \le L_2(\theta_2).$$
