# Design-unbiasedness of the exposure mean estimator under consistency

Let $U$ be a finite set of $N$ units, $\Omega$ a set of assignments, $e : U \times \Omega \to \Delta$ an exposure mapping, $p$ a probability mass function (design) on $\Omega$, and $y^r : U \times \Omega \to \mathbb R$ randomization potential outcomes, so $y^r_i(z)$ is the observed outcome of unit $i$ at the realized assignment $z$. Let $\pi_i(d) = p(\{z : e_i(z) = d\})$ be the exposure probabilities. Assume $\Omega$ is countable with measurable singletons, and give the finitely many subsets of $U$ the discrete $\sigma$-algebra; a countably supported law on an uncountable assignment space is not covered. Fix an exposure $d$ and potentials $y : U \times \Delta \to \mathbb R$ with $y^r_i(z) = y_i(e_i(z))$ for every unit $i$ and every assignment $z$ with $p(z) \ne 0$. If $\pi_i(d) > 0$ for every unit $i$, then the mean estimator $\hat y^T_{HT}(d) / N$, where $\hat y^T_{HT}(d)(z) = \sum_{i : e_i(z) = d} y^r_i(z) / \pi_i(d)$, is design-unbiased for the mean potential outcome:

$$\mathbb E_{z \sim p}\Bigl[\frac{\hat y^T_{HT}(d)(z)}{N}\Bigr] = \frac1N \sum_{i \in U} y_i(d).$$

With the convention $x / 0 = 0$, the identity also holds for $N = 0$.
