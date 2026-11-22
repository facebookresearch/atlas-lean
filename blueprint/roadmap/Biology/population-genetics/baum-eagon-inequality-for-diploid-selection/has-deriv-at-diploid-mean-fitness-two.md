# Derivative of two-allele mean fitness

Let $w$ be a real $2 \times 2$ matrix of genotype fitnesses. For every real $x$, the function

$$\bar w(y) = y^2 w_{00} + y(1 - y)(w_{01} + w_{10}) + (1 - y)^2 w_{11},$$

the mean fitness at the allele frequencies $(y, 1 - y)$, has derivative $2(m_0 - m_1)$ at $x$, where $m_i = \sum_j \frac{w_{ij} + w_{ji}}{2} p_j$ are the marginal fitnesses at $p = (x, 1 - x)$.
