# Existence and uniqueness of maximum-likelihood item difficulties in the Rasch model

In the Rasch model, persons $v = 1, \dots, N$ with abilities $\theta_v$ answer items $i = 1, \dots, k$ with difficulties $\beta_i$, and the responses $X_{vi} \in \{0, 1\}$ are independent with

$$\mathbb P(X_{vi} = 1) = \frac{\exp(\theta_v - \beta_i)}{1 + \exp(\theta_v - \beta_i)}.$$

The difficulties are identified only up to a common shift, so normalize $\sum_i \beta_i = 0$. Maximum-likelihood estimates of the difficulties need not exist for every data set. For example, with $k = 2$ items, suppose every person with raw score $1$ answers item $1$ correctly and item $2$ incorrectly. Given raw score $1$, the response $(1, 0)$ has conditional probability $e^{-\beta_1} / (e^{-\beta_1} + e^{-\beta_2})$, which along the normalized path $(\beta_1, \beta_2) = (-b, b)$ equals $1/(1 + e^{-2b})$; the conditional likelihood increases to its supremum $1$ as $b \to \infty$ and attains no maximum. Fischer's theorem: after removing persons with raw score $0$ or $k$, the conditional maximum-likelihood estimate of $(\beta_1, \dots, \beta_k)$, given the persons' raw scores, exists and is unique if and only if the directed graph on the items, with an edge from $i$ to $j$ whenever some person answers $i$ correctly and $j$ incorrectly, is strongly connected.

## Expansion

This page becomes ready once:

- the Rasch family and the conditional likelihood given raw scores are fixed as a statement prerequisite (statement prerequisite)
- Fischer's condition is proved by strict concavity of the conditional log-likelihood on the normalized parameter space and coercivity under strong connectivity (proof obligation)

## Sources

- G. H. Fischer, "On the existence and uniqueness of maximum-likelihood estimates in the Rasch model", *Psychometrika* 46(1):59–77, 1981
- G. Rasch, *Probabilistic Models for Some Intelligence and Attainment Tests*, Danish Institute for Educational Research, 1960
