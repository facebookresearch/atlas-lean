# Interpolants of bounded model checking refutations over-approximate images

Let $(I, T)$ be a transition system with bad states $B$ and $k \ge 1$. Let $A = I(s_0) \wedge T(s_0, s_1)$ and $B_k = T(s_1, s_2) \wedge \cdots \wedge T(s_{k-1}, s_k) \wedge \bigvee_{i=1}^{k} B(s_i)$. If $A \wedge B_k$ is unsatisfiable and $J(s_1)$ is an interpolant for $(A, B_k)$ (so $A \Rightarrow J$ and $J \wedge B_k$ is unsatisfiable, and $J$ mentions only $s_1$), then $J$ contains the image of $I$ under $T$ and no bad state is reachable from $J$ in fewer than $k$ steps.

## Proof depends on

- [Interpolants from resolution refutations](../../../Logic/propositional-logic/proof-certificates/interpolants-from-resolution-refutations.md)
- [Bounded model checking for existential LTL](bounded-model-checking-for-existential-ltl.md)

## Sources

- K. L. McMillan, "Interpolation and SAT-based model checking", *CAV 2003*, LNCS 2725, Springer, 2003
