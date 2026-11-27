# Strengthened induction with depth

Let $T$ be a transition relation in which every state has a successor, with initial states $I$ and property $P$, and let $i \ge 0$. Suppose that

- (base) every path $s_0, \dots, s_i$ with $s_0 \in I$ has all of its states in $P$, and
- (step) every [loop-free path](loop-free-paths-of-a-transition-system.md) $s_0, \dots, s_{i+1}$ whose first $i + 1$ states are in $P$ ends in a state $s_{i+1} \in P$, or else no loop-free path $s_0, \dots, s_{i+1}$ has $s_0 \in I$ and $s_1, \dots, s_{i+1} \notin I$.

Then the system is $P$-safe. Without the restriction to loop-free paths in the step, induction with depth is incomplete; with it, on a finite state space some depth $i$ satisfies the conditions whenever the system is $P$-safe, and this forward procedure is equivalent to the procedure of [induction over loop-free paths](induction-over-loop-free-paths-decides-safety.md). The case $i = 0$ without the loop-free restriction is the inductive-invariant argument of [safety by inductive invariants](safety-by-inductive-invariants.md).

## Depends on

- [Loop-free paths of a transition system](loop-free-paths-of-a-transition-system.md)

## Proof depends on

- [Induction over loop-free paths decides safety](induction-over-loop-free-paths-decides-safety.md)

## Related topics

- [Safety by inductive invariants](safety-by-inductive-invariants.md)

## Sources

- M. Sheeran, S. Singh and G. Stålmarck, "Checking safety properties using induction and a SAT-solver", *Formal Methods in Computer-Aided Design (FMCAD 2000)*, LNCS 1954, Springer, 2000, pp. 108–125, Section 3, Algorithm 4 and the discussion of strengthened induction with depth after it.
