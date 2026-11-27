# Observed likelihood proportional under realized MAR

Let $Y$ be a countable outcome space with a normalized density family $f_\theta$ (counting measure), $g_\psi(y)$ a missingness law over patterns $M$, and $o(y, m)$ the observed part. Fix observed data $(y_0, m_0)$ and a parameter set $S \subseteq \Theta \times \Psi$ that is a product of its projections $S_\Theta \times S_\Psi$ (variation independence). Assume realized missing at random: for every $\psi \in S_\Psi$, $g_\psi(y)(m_0) = g_\psi(y')(m_0)$ whenever $o(y, m_0) = o(y', m_0) = o(y_0, m_0)$. Let $\psi \in S_\Psi$ with $c = g_\psi(y_0)(m_0) \ne 0$. Then $0 < c \le 1$ and for every $\theta$,

$$L_1(\theta, \psi) = c\,L_2(\theta),$$

where $L_1(\theta, \psi) = \mathbf 1_S(\theta, \psi) \sum_{y : o(y, m_0) = o(y_0, m_0)} f_\theta(y)\,g_\psi(y)(m_0)$ and $L_2(\theta) = \mathbf 1_{S_\Theta}(\theta) \sum_{y : o(y, m_0) = o(y_0, m_0)} f_\theta(y)$.

This is Theorem 1(ii) of S. R. Seaman, J. Galati, D. Jackson and J. Carlin, What is meant by "missing at random"?, *Statistical Science* 28 (2013).
