# BDe family score as a ratio of marginal likelihoods

Let $V$ be a finite set of variables, each $v \in V$ taking values in a finite set $\sigma_v$, let
$p : \prod_v \sigma_v \to \mathbb{R}$, $\mathrm{ess} \in \mathbb{R}$ and $D$ a finite list of
cases. For finite sets $P \subseteq F \subseteq V$, the
[Bayesian–Dirichlet family score](bd-family.md) of $F$ with parent set $P$ and the
[BDe hyperparameters](bde-hyper.md) of $F$ is the ratio of the
[BDe marginal likelihoods](marg-lik.md) of $F$ and of $P$:

$$\mathrm{BD}_F\big(D; \alpha^{\mathrm{BDe}}_F\big) = \frac{L(D, F)}{L(D, P)},$$

with the convention that a quotient by $0$ is $0$.
