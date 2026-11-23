# Monotonicity of the Poisson-binomial tail in the success probabilities

Let $p, q \in [0, 1]^m$ with $p_i \le q_i$ for every $i$. Then for every $k \in \mathbb{N}$,
$T_k(p) \le T_k(q)$, where $T_k(p) = \sum_{j=k}^{m} \pi_p(j)$ is the upper tail of the Poisson-binomial
law: the probability of at least $k$ successes among independent trials with success probabilities
$p_0, \dots, p_{m-1}$.

## Idea

Raising the success probability of a trial can only make many successes more likely. The law does not
depend on the order of the trials, so it is enough to raise one probability, say $p_0$. Conditioning on
the first trial gives $T_k(p) = p_0\, T_{k-1}(p') + (1 - p_0)\, T_k(p')$ for $k \ge 1$, where $p'$ lists
the other trials, and this is nondecreasing in $p_0$ because $T_{k-1}(p') \ge T_k(p')$. In genetic
burden tests the $p_i$ are background mutation rates and the tail is the p-value, so overestimating a
rate can only make the test more conservative.

## Statements

- [The burden-test p-value is monotone in every background rate](poisson-binomial-tail-mono.md)
- [Binomial tail monotonicity](binomial-tail-mono.md): the binomial special case
- [Binomial upper tail is monotone in the success probability](binomial-real-ici-mono.md): the binomial special case, for the binomial law as a measure

## Background

- [Poisson-binomial distribution](../poisson-binomial-law/README.md): the upper tail and its recurrence
