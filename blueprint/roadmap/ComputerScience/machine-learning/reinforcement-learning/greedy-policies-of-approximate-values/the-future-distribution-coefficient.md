# The future distribution coefficient

Let $X$ and $A$ be the finite nonempty state and action sets of a Markov
decision process. Write $p(x,a,y)$ for the real probability of moving from
$x$ to $y$ under action $a$, with $p(x,a,y)\ge 0$ for every $x,y\in X$ and
$a\in A$ and $\sum_{y\in X}p(x,a,y)=1$ for each $(x,a)$. Let $\nu$ and $\mu$
be probability mass functions on $X$, each with nonnegative entries summing
to $1$. Regard them as row vectors indexed by $X$, with $\nu$ the initial
law and $\mu$ the reference law.

For a deterministic decision rule $\pi:X\to A$, use the transition matrix
$P^\pi$ with entries $P^\pi(x,y)=p(x,\pi(x),y)$. For an integer $m\ge 1$,
choose a rule $\pi_i:X\to A$ for each step $i=1,\ldots,m$. The rules need
not be the same at each step. Starting at $\nu$, apply the matrices by
multiplication on the right: $P^{\pi_1}$ first, then $P^{\pi_2}$, and so on.
The future distribution concentration coefficient at time $m$ is the
extended nonnegative real

$$
c(m)=\max_{\pi_1,\ldots,\pi_m:X\to A,\ y\in X}
\frac{(\nu P^{\pi_1}P^{\pi_2}\cdots P^{\pi_m})(y)}{\mu(y)}.
$$

When $\mu(y)>0$ the ratio is the ordinary quotient. At $\mu(y)=0$, use
$0/0=0$ and $u/0=+\infty$ for every positive numerator $u$.

Separately, set $c(0)=1$ by convention, independently of $\nu$ and $\mu$.
The ratio formula is only for positive times.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic Markov decision process](../../../heuristic-search-and-planning/value-iteration/stochastic.md)
- [Transition matrix of a stationary policy](../../../heuristic-search-and-planning/stochastic-shortest-path-problems/transition-matrix.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Sources

- R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007). [Author manuscript, HAL inria-00124685 v1](https://inria.hal.science/inria-00124685v1/document), §5.1, Definition 5.1, equation (5.1) and the following convention (manuscript p. 9).
