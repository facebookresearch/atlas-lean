# The Bayes posterior integrates a Gaussian mixture correctly

Let $p \in (0, 1)$, $m_0, m_1 \in \mathbb{R}$, $s > 0$, and $q$ the Bayes posterior for the densities of $\mathcal N(m_0, s)$ and $\mathcal N(m_1, s)$. For every measurable $A$,

$$p\int_A q\,d\mathcal N(m_1, s) + (1 - p)\int_A q\,d\mathcal N(m_0, s) = p\,\mathcal N(m_1, s)(A).$$
