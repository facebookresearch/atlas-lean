# First-moment phenotype model of SLDP regression

Let $P$ be a measure on a measurable space $\Omega$ and let $N, M$ be natural numbers (individuals and markers). A first-moment SLDP model consists of a vector $m \in \mathbb{R}^M$ (the mean effects) and real functions $\beta_1, \dots, \beta_M$ (the effects) and $\varepsilon_1, \dots, \varepsilon_N$ (the noise) on $\Omega$, all $P$-integrable, with

$$\int \beta_k \, dP = m_k \quad\text{and}\quad \int \varepsilon_i \, dP = 0$$

for all $k$ and $i$. SLDP regression takes $m = \mu v$ for a signed annotation $v \in \mathbb{R}^M$; no second-moment condition is imposed.
