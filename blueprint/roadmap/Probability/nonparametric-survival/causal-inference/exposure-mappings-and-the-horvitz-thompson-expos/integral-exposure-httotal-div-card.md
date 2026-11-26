# Design-unbiasedness of the mean estimator under the design-free Condition 1

Let $U$ be a finite set of $N$ units, $\Omega$ a set of assignments, $e : U \times \Omega \to \Delta$ an exposure mapping, $p$ a probability mass function (design) on $\Omega$, and $y^r : U \times \Omega \to \mathbb R$ randomization potential outcomes, so $y^r_i(z)$ is the observed outcome of unit $i$ at the realized assignment $z$. Let $\pi_i(d) = p(\{z : e_i(z) = d\})$ be the exposure probabilities. Assume $\Omega$ is countable with measurable singletons, and give the finitely many subsets of $U$ the discrete $\sigma$-algebra; a countably supported law on an uncountable assignment space is not covered. Suppose the exposure mapping is sufficient: $e_i(z) = e_i(z')$ implies $y^r_i(z) = y^r_i(z')$ for every unit $i$ and all assignments $z, z'$. Let $y_i(d)$ be the exposure-specific potential outcome ($y^r_i$ at a chosen assignment giving unit $i$ exposure $d$, and $0$ if there is none). Fix $d$ with $\pi_i(d) > 0$ for every unit $i$. Then the mean estimator is design-unbiased for Aronow and Samii's estimand $\mu(d) = \frac1N \sum_i y_i(d)$:

$$\mathbb E_{z \sim p}\Bigl[\frac{\hat y^T_{HT}(d)(z)}{N}\Bigr] = \frac1N \sum_{i \in U} y_i(d),$$

where $\hat y^T_{HT}(d)(z) = \sum_{i : e_i(z) = d} y^r_i(z) / \pi_i(d)$. With the convention $x / 0 = 0$, the identity also holds for $N = 0$.
