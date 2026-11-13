# A greedy policy for the optimal value is optimal

Let $M$ be a Markov decision process
with finitely many states, finitely many actions (at least one), real rewards $r(s,a)$, and
transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, let
$0 \le \gamma < 1$, and let $V^*$ be the optimal value. Let $\pi$ be the greedy policy for
$V^*$, which in each state $s$ chooses an action $a$ maximizing
$r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V^*(s')$. Then the value of $\pi$ equals $V^*$.
