# BDe marginal likelihood of a variable set

Let $V$ be a finite set of variables, each $v$ taking values in a finite set $\sigma_v$, let
$p : \prod_v \sigma_v \to \mathbb{R}$, $\mathrm{ess} \in \mathbb{R}$ and $D$ a finite list of
cases. For a finite $S \subseteq V$, the BDe marginal likelihood of $S$ is

$$L(D, S) = \prod_{c} \big(\alpha^{\mathrm{BDe}}_S(c)\big)^{\overline{N_S(c)}},$$

the product over the configurations $c$ of $S$ of the [rising factorial](rising.md) of the
[BDe hyperparameter](bde-hyper.md) of $c$ to the [count](count.md) of $c$ in $D$. This is the
(unnormalized) marginal likelihood of the data restricted to $S$ under the BDe Dirichlet prior on
the joint values of $S$ when the state sets $\sigma_v$ are nonempty and the [BDe hyperparameters](bde-hyper.md) are
positive (for instance $p > 0$ and $\mathrm{ess} > 0$); in general it is the same algebraic expression, with $p$ treated as generalized weights: the total Dirichlet mass over
configurations is $\mathrm{ess} \sum_x p(x)$, so the omitted normalizing factor is
$1 / (\mathrm{ess} \sum_x p(x))^{\overline{|D|}}$, the same for every $S$. When
$\sum_x p(x) = 1$ this is $1 / \mathrm{ess}^{\overline{|D|}}$, and when moreover $p \ge 0$, $p$ is a prior
joint distribution.
