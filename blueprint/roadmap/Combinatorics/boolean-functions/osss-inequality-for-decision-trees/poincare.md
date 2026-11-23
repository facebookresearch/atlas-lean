# Poincaré inequality for Boolean functions under a product measure

Let $E$ be a finite set, $\nu$ a [product probability weight](is-prob-weight.md) on $\{0, 1\}^E$ and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$. Then

$$\mathrm{Var}_\nu(f) \le \sum_{e \in E} \mathrm{Inf}_e(f),$$

where $\mathrm{Inf}_e(f)$ is the probability under $\nu$ that $e$ is pivotal for $A$. This is the OSSS inequality for the [decision tree that queries every variable](full-tree-univ.md); it is weaker than the Efron–Stein inequality $\mathrm{Var}(f) \le \sum_e p_e(1 - p_e)\, \mathbb{E}[(\partial_e f)^2]$, where $p_e = \nu_e(1)$, by the factor $p_e(1 - p_e) \le 1/4$.
