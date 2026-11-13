# Bellman optimality operator

Let $M$ be a Markov decision process with finitely many
states $s$, a nonempty finite set of actions $a$, rewards $r(s, a)$ and transition probabilities
$p(s, a, s')$ in a field $K$ carrying a linear order, and let $\gamma \in K$ be a discount factor.
The Bellman optimality operator $T$ sends a function $V$ from states to $K$ to the function

$$(TV)(s) = \max_a \Big( r(s, a) + \gamma \sum_{s'} p(s, a, s') V(s') \Big),$$

the largest action value in state $s$.
