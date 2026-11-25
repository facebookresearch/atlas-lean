# Likelihood factorization under missing at random

Let $F_\theta$ be a family of probability mass functions on a countable outcome space, $g_\psi(y)$ a law of the missingness pattern given $y$, $o(y, m)$ the observed part of $y$ under pattern $m$, and $(y_0, m_0)$ a realized observation. Suppose the missingness probability $g_\psi(y)(m_0)$ is the same for all $y$ consistent with the observed data $o(y_0, m_0)$, for every $\psi$ in the parameter set $S$ (realized MAR), and $S$ is a product of its $\theta$- and $\psi$-projections (variation independence). Then the observed-data likelihood $\sum_{y : o(y,m_0) = o(y_0,m_0)} F_\theta(y)\, g_\psi(y)(m_0)$, restricted to $S$, equals $g_\psi(y_0)(m_0)$ times $\sum_{y : o(y,m_0) = o(y_0,m_0)} F_\theta(y)$, each factor restricted to its projection of $S$.

## Sources

- S. Seaman, J. Galati, D. Jackson and J. Carlin, "What is meant by 'missing at random'?", Statistical Science 28 (2013), Theorem 1(i).
