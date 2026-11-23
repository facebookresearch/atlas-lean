# The greedy action attains the Bellman maximum

Let $M$ be a Markov decision process
with a finite set of states $S$, a finite nonempty set of actions, and rewards $r(s,a)$ and
transition probabilities $P(s,a,s')$ in a field $K$ with a linear order, and let $\gamma \in K$.
For every $V : S \to K$ and every state $s$, the action $g$ that the greedy policy for $V$
chooses in $s$ satisfies
$r(s,g) + \gamma \sum_{s'} P(s,g,s') \, V(s') =
\max_a \bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V(s')\bigr)$, so its action value equals
the value of the Bellman optimality operator applied to $V$ at $s$.
