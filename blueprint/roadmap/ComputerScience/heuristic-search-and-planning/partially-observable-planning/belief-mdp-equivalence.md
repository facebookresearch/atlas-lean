# Belief MDP equivalence (finite horizon)

Let a finite POMDP have states $S$, actions $A$, observations $O$, transitions $P$, observation
probabilities $Z$, rewards $r$ and an initial belief $b_0$, and fix a horizon $H \ge 0$ with terminal
reward $0$. Define the belief MDP on $\Delta(S)$ with reward $\rho(b, a) = \sum_s b(s) r(s,a)$ and, from
$b$ under $a$, transition to $\tau(b, a, o)$ with probability $\Pr(o \mid b, a)$ for each $o$ with
$\Pr(o \mid b, a) > 0$. Then the supremum over history-dependent randomized policies of the expected
$H$-step reward from $b_0$ equals the $H$-step value $V_H(b_0)$ of the belief MDP computed by backward
induction ($V_0 = 0$, $V_{h+1}(b) = \max_a [\rho(b,a) + \sum_{o : \Pr(o \mid b,a) > 0} \Pr(o \mid b, a) V_h(\tau(b,a,o))]$),
and a policy that applies a backward-induction maximizer to the current belief attains it.
Observations of zero predictive probability do not occur and need no update.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: Finite-horizon backward induction.

## Depends on

- [Finite POMDPs](finite-pomdps.md)
- [Belief update](belief-update.md)
- [History-dependent randomized policies and trajectory laws](../markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)

## Sources

- L. P. Kaelbling, M. L. Littman and A. R. Cassandra, *Planning and acting in partially observable stochastic domains*, Artificial Intelligence 101 (1998) 99–134, Section 3.4: the belief state is a sufficient statistic and the optimal policy solves the belief MDP with transitions $t(b, a, b')$ and reward $\rho(b, a)$; the finite-horizon value recursion over beliefs is in Section 4. <https://cs.brown.edu/courses/csci2951-k/papers/kaelbling98.pdf>
