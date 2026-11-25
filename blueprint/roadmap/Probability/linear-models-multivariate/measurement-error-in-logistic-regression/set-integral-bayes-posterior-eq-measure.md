# The Bayes posterior is a version of the conditional probability

Let $Y$ be a measurable binary label and $Z$ a measurable real random variable on a probability space with $p = P(Y = 1) \in (0, 1)$, such that conditionally on $Y = y$, $Z$ has law $\mathcal N(m_y, s)$ with $s > 0$. Let $q$ be the Bayes posterior for the densities of $\mathcal N(m_0, s)$ and $\mathcal N(m_1, s)$ and prior $p$. Then for every measurable $A$, $\int_{\{Z \in A\}}q(Z)\,dP = P(Y = 1,\ Z \in A)$.
