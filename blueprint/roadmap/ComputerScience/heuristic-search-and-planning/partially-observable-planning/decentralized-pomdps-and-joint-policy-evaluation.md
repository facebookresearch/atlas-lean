# Decentralized POMDPs and joint-policy evaluation

This node collects the model of decentralized POMDPs and the complexity of evaluating a fixed joint
policy.

## Expansion

A sound expansion has separate pages for:

1. **Model.** An $m$-agent DEC-POMDP has a finite state set, for each agent a finite action set and a
   finite observation set, a joint transition probability, a joint observation probability and a shared
   reward; for horizon $T$, a local policy of agent $i$ is a map from agent $i$'s own observation
   histories of length less than $T$ to its actions, represented as an explicit policy tree.
2. **Joint-policy value.** The value of a joint policy from an initial state distribution is the
   expected total reward over $T$ steps, a finite sum over joint histories.
3. **Evaluation complexity.** For a fixed number $m$ of agents, the value of an explicitly given joint
   policy is computable in time polynomial in the size of the model and of the $m$ policy trees (with
   the encoding of probabilities and rewards stated); without fixing $m$ the statement needs its own
   source.

## Depends on

- [Finite POMDPs](finite-pomdps.md)

## Sources

- D. S. Bernstein, R. Givan, N. Immerman and S. Zilberstein, *The complexity of decentralized control of Markov decision processes*, Mathematics of Operations Research 27(4) (2002) 819–840: the DEC-POMDP model and local policies (Section 2) and the proof of Theorem 1, which evaluates a given joint policy through the POMDP over joint observations. For a fixed number of agents the number of joint observation histories is the product of the agents' history counts, which gives the polynomial bound of item 3. <http://www.cs.umass.edu/~immerman/pub/bgiz.pdf>
