# Transition concentration coefficient

Let $X$ and $A$ be the finite nonempty state and action sets of a Markov
decision process. Write $p(x,a,y)$ for the real probability of moving from
$x$ to $y$ under action $a$, with $p(x,a,y)\ge 0$ for every $x,y\in X$ and
$a\in A$ and $\sum_{y\in X}p(x,a,y)=1$ for each $(x,a)$. Let $\mu$ be a
probability mass function on $X$: its entries are nonnegative and sum to $1$.

The transition concentration coefficient relative to $\mu$ is the extended
nonnegative real

$$
C(\mu)=\max_{x,y\in X,\ a\in A}\frac{p(x,a,y)}{\mu(y)}.
$$

When $\mu(y)>0$ the ratio is the ordinary quotient. At $\mu(y)=0$, use
$0/0=0$ and $u/0=+\infty$ for every positive numerator $u$.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic Markov decision process](../../../heuristic-search-and-planning/value-iteration/stochastic.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Sources

- R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007). [Author manuscript, HAL inria-00124685 v1](https://inria.hal.science/inria-00124685v1/document), §5.1, Definition 5.1 (manuscript p. 9).
