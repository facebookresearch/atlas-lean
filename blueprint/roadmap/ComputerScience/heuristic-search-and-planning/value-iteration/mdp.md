# Markov decision process

A Markov decision process with states in $S$, actions in $A$ and
values in $K$ consists of a reward $r(s, a) \in K$ for taking action $a$ in state $s$ and, for all
states $s, s'$ and actions $a$, a value $p(s, a, s') \in K$, the probability of moving from $s$ to
$s'$ under action $a$.

No condition is imposed here: finiteness of the states and actions, an order on $K$ and the
stochasticity of $p$ are hypotheses of the results that use them.
