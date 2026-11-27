# Belief update

For a finite POMDP with states $S$, transition probabilities $P(s' \mid s, a)$ and observation
probabilities $Z(o \mid s', a)$, a belief is a probability distribution $b$ on $S$. The predictive
probability of observation $o$ after action $a$ is
$\Pr(o \mid b, a) = \sum_{s'} Z(o \mid s', a) \sum_s P(s' \mid s, a)\, b(s)$. When it is positive, the
updated belief is

$$\tau(b, a, o)(s') = \frac{Z(o \mid s', a) \sum_s P(s' \mid s, a)\, b(s)}{\Pr(o \mid b, a)}.$$

The update is undefined for observations of zero predictive probability; any convention for that case
(for example, leaving the belief unchanged) is a separate choice that no statement may rely on.

## Depends on

- [Finite POMDPs](finite-pomdps.md)

## Sources

- L. P. Kaelbling, M. L. Littman and A. R. Cassandra, *Planning and acting in partially observable stochastic domains*, Artificial Intelligence 101 (1998) 99–134, Section 3.3: the state estimator $SE(b, a, o)$ and its normalizing factor $\Pr(o \mid a, b)$. <https://cs.brown.edu/courses/csci2951-k/papers/kaelbling98.pdf>
