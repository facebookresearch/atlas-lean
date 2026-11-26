# KKL inequality for $p$-biased measures

For every $p \in (0, 1)$ there is a constant $c > 0$ such that for every finite nonempty set $E$ and every set $A \subseteq \{0, 1\}^E$, with $f = 1_A$,

$$c\, \mathrm{Var}_p(f) \log \frac{1}{\max_{e \in E} \mathrm{Inf}^p_e} \le \sum_{e \in E} \mathrm{Inf}^p_e,$$

where $\mathrm{Inf}^p_e$ is the probability under the $p$-biased product measure $\mu_p$ that $e$ is pivotal for $A$, and $\log(1/0)$ is read as $0$.

Talagrand's inequality $\mathrm{Var}_p(f) \le K(p) \sum_e \mathrm{Inf}^p_e / \log\big(1/(p(1-p)\mathrm{Inf}^p_e)\big)$ gives this with $c = 1/K(p)$, since each $\mathrm{Inf}^p_e$ is at most the maximal influence.

## Sources

- M. Talagrand, *On Russo's approximate zero-one law*, Ann. Probab. 22 (1994); J. Bourgain, J. Kahn, G. Kalai, Y. Katznelson, N. Linial, *The influence of variables in product spaces*, Israel J. Math. 77 (1992).
