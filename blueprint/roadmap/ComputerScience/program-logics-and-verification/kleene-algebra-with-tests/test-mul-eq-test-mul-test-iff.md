# Postcondition absorption characterizes partial correctness

Let $W$ be a set of states. Binary relations on $W$ are composed sequentially, $R \cdot S = \{(s, u) : (s, t) \in R \text{ and } (t, u) \in S \text{ for some } t\}$, with unit the identity relation $1$, and ordered by inclusion. For an assertion $P \subseteq W$, the test $[P] = \{(s, s) : s \in P\}$ is the [diagonal test relation](test-set.md) of $P$. For a relation $R$ and an assertion $Q$, write $\mathrm{core}_R(Q) = \{s : t \in Q \text{ whenever } (s, t) \in R\}$ for the set of states all of whose $R$-successors lie in $Q$. For all assertions $P, Q \subseteq W$ and every relation $R$ on $W$,

$$[P] \cdot R = [P] \cdot R \cdot [Q] \iff P \subseteq \mathrm{core}_R(Q):$$

the postcondition $Q$ can be absorbed on the right exactly when it holds at the end of every execution of $R$ starting in $P$.
