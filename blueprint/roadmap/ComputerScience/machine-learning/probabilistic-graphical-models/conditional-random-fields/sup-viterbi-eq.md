# Viterbi computes the MAP value of a chain CRF

Let $c$ be a chain conditional random
field with a finite nonempty set of states $S$ and weights in a linearly ordered commutative
semiring $R$, and let $x$ be an observation sequence. For every $t \in \mathbb{N}$, the maximum
over $s \in S$ of the Viterbi variable $V_t(s)$ of $c$ at $x$ equals the maximum, over all label
paths $z : \{0, \dots, t\} \to S$, of the weight of $z$.
