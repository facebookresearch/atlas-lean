# Finite POMDPs

A finite POMDP consists of a finite MDP (states $S$, actions $A$, transition probabilities
$P(s' \mid s, a)$, rewards $r(s, a)$), a finite observation set $O$ and observation probabilities
$Z(o \mid s', a)$: after action $a$ is taken in state $s$, the next state $s'$ is drawn from $P(\cdot \mid s,a)$
and then an observation $o$ is drawn from $Z(\cdot \mid s', a)$. The initial state is drawn from an initial
belief $b_0$. A policy maps each action-observation history $(a_0, o_1, \dots, a_{t-1}, o_t)$ to a
probability distribution on $A$; it never sees states. The finite-horizon value with terminal reward
$0$ and, for $0 \le \gamma < 1$, the discounted value are the expected total (discounted) rewards under
the trajectory law induced by $b_0$, the policy, $P$ and $Z$.

## Depends on

- [Markov decision process](../value-iteration/mdp.md)
- [History-dependent randomized policies and trajectory laws](../markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)

## Sources

- L. P. Kaelbling, M. L. Littman and A. R. Cassandra, *Planning and acting in partially observable stochastic domains*, Artificial Intelligence 101 (1998) 99–134, Section 3.1: the POMDP tuple with observation function $O(s', a, o)$, observations drawn after the transition. <https://cs.brown.edu/courses/csci2951-k/papers/kaelbling98.pdf>
