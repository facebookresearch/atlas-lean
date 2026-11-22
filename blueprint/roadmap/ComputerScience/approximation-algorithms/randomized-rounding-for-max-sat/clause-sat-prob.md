# Satisfaction probability of a clause

For a clause $C$, a list of literals $(i, b)$ (the literal $x_i$ when $b$ is true and $\bar x_i$
when $b$ is false) with positive variables $P$ and negated variables $N$, and probabilities
$0 \le p_i \le 1$,

$$1 - \prod_{\ell \in C} \left(1 - \Pr[\ell \text{ true}]\right) = 1 - \prod_{i \in P}(1 - p_i) \prod_{i \in N} p_i .$$

The literals of $C$ use distinct variables. When each variable $x_i$ is set true independently
with probability $p_i$, this is the probability that $C$ is [satisfied](../../../Logic/propositional-logic/conjunctive-normal-form/satisfies-2.md): exactly one assignment of
the variables of $C$ falsifies it, and its weight is the product.

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), §2.
