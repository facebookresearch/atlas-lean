# Exchangeability of the IBSS posterior under identical predictors

Suppose two columns $x_j$ and $x_k$ ($j \ne k$) of the design matrix $X$ are identical ($x_j = x_k$)
and have equal prior inclusion probabilities ($\pi_j = \pi_k$). If IBSS is initialized symmetrically
in coordinates $j$ and $k$, then at every iteration (and at convergence) the IBSS approximate posterior
$q$ is exchangeable in $(j, k)$: for the coordinate-swap map $\omega_{jk} : \mathbb{R}^p \to \mathbb{R}^p$,
each factor satisfies $q_l \circ \omega_{jk} = q_l$. In particular, variables $j$ and $k$ receive
equal posterior inclusion probabilities in every single-effect component.

## Depends on

- [Sum of Single Effects (SuSiE) model and factored variational family](sum-of-single-effects-model.md)
- [IBSS coordinate-ascent update reduces to single-effect regression](ibss-coordinate-ascent-ser-update.md)

## Expansion

Because $x_j = x_k$ and $\pi_j = \pi_k$, the single-effect Bayes factors and conditional posterior
moments computed by $\operatorname{SER}(X, \bar r_l; \sigma^2, \sigma_{0l}^2)$ depend on
$j$ and $k$ only through $(x_j^\top \bar r_l, \|x_j\|_2^2, \pi_j)$, which are identical.
By induction on the IBSS steps, exchangeability of every $q_l$ in $(j, k)$ is preserved.

## Sources

- G. Wang, A. Sarkar, P. Carbonetto, and M. Stephens, "A Simple New Approach to Variable Selection in Regression, with Application to Genetic Fine Mapping", Journal of the Royal Statistical Society Series B 82 (2020), 1273–1300, <https://doi.org/10.1111/rssb.12388> (PMC10201948). (Proposition 3.)
