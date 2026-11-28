# Marginal point mass of the event time as a sum over causes

Let $k$ and $r$ be natural numbers and let $p$ be a probability mass function on $\{0, \dots, k-1\} \times \{0, \dots, r-1\}$, the joint law of an event time $T$ and a cause $J$. Let $p_T$ be its image under the projection $(l, c) \mapsto l$, the marginal law of $T$.

For every grid index $l$,

$$p_T(l) = \sum_{c=0}^{r-1} p(l, c),$$

where both sides are the point masses converted to real numbers.
