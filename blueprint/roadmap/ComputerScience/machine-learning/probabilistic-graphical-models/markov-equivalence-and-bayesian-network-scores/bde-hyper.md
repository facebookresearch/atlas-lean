# BDe hyperparameters

BDe hyperparameters (Heckerman, Geiger and Chickering): let $V$ be a finite set of variables,
each $v$ taking values in a finite set $\sigma_v$, let $p : \prod_v \sigma_v \to \mathbb{R}$ and
$\mathrm{ess} \in \mathbb{R}$. For a finite $S \subseteq V$ and a configuration $c$ of $S$, the
BDe hyperparameter is $\mathrm{ess} \cdot \sum_{x \,:\, x_S = c} p(x)$. When
$p \ge 0$ and $\sum_x p(x) = 1$, $p$ is a prior joint distribution and the sum is the prior probability of $c$;
for nonempty state sets $\sigma_v$, the hyperparameters are proper Dirichlet concentrations when they are
all positive, for instance for $p > 0$ and $\mathrm{ess} > 0$.
