# Safety monotonicity and the frame property

Safety monotonicity says that a command safe on a state stays safe on every larger state; the frame property says that every outcome from a larger state arises from the safe smaller state with the added part unchanged. Termination monotonicity is the analogue for must-termination, needed only for total correctness.

*Abstract form.* Let $(\Sigma, \bullet, u)$ be a [separation algebra](../abstract-separation-logic/separation-algebras.md) and $R \subseteq \Sigma \times (\Sigma \cup \{\mathit{fault}\})$, where $(\sigma, \sigma') \in R$ means that the program can deliver $\sigma'$ when started in $\sigma$ and $(\sigma, \mathit{fault}) \in R$ means that it can fault; $R$ is *safe at* $\sigma$ if $(\sigma, \mathit{fault}) \notin R$. A state may have both faulting and normal outcomes, and a state with no outcome at all is one from which the program only diverges.

- *Safety monotonicity*: if $R$ is safe at $\sigma$ and $\sigma \preceq \sigma'$, then $R$ is safe at $\sigma'$.
- *Frame property*: if $R$ is safe at $\sigma_0$, $\sigma = \sigma_0 \bullet \sigma_1$ and $(\sigma, \sigma') \in R$, then $\sigma' = \sigma_0' \bullet \sigma_1$ for some $\sigma_0'$ with $(\sigma_0, \sigma_0') \in R$.

*Operational form.* Consider a small-step relation $\leadsto$ on configurations $C, s, h$ of a command $C$, a store $s$ and a heap $h$, where heaps carry a partial combination $\ast$, together with terminal states $s, h$ and a fault configuration, as for the heap language. A configuration is *safe* if no fault is reachable from it, and *must terminate normally* if it is safe and has no infinite execution. A configuration is *stuck* if it is neither terminal nor the fault and has no step; a command has *progress* if no configuration reachable from it is stuck. With $h \# h'$ meaning that $h \ast h'$ is defined,

- *safety monotonicity*: if $C, s, h$ is safe and $h \# h'$, then $C, s, h \ast h'$ is safe;
- *termination monotonicity*: if $C, s, h$ must terminate normally and $h \# h'$, then $C, s, h \ast h'$ must terminate normally;
- *frame property*: if $C, s, h_0$ is safe and $C, s, h_0 \ast h_1 \leadsto^\ast s', h'$, then $C, s, h_0 \leadsto^\ast s', h_0'$ for some $h_0'$ with $h' = h_0' \ast h_1$.

Safety concerns faults only, so a diverging execution is safe; and must-termination as defined here does not by itself provide a terminal state, since a stuck configuration has no infinite execution.

The tempting stronger property that every execution from $h_0$ can be replayed from $h_0 \ast h_1$ with $h_1$ added unchanged fails, because allocation from a small heap may pick an address already in use in a larger one: locality is a property of all executions from a safe state, not of each execution. A Petri net with capacity $1$, markings combined by disjoint union and a disabled transition read as a fault, violates safety monotonicity: a transition with pre-set $\{a\}$ and post-set $\{b\}$, $a \neq b$, is enabled at $\{a\}$ but not at $\{a, b\}$. An operation that traps memory faults would likewise violate safety monotonicity, since a program could branch on whether a cell is allocated.

## Depends on

- [Separation algebras](../abstract-separation-logic/separation-algebras.md)

## Proof depends on

None.

## Expansion

Under progress, a configuration that must terminate normally reaches a terminal state along every maximal execution: such an execution is finite, its last configuration has no step, is not stuck by progress and is not the fault by safety, so it is terminal. Whether the commands of a given language have these properties is a theorem about its semantics; for the heap language of Yang and O'Hearn, in which every non-terminal configuration steps or faults, so that every command has progress, it is [heap-language commands are safety monotone, termination monotone and framing](heap-language-commands-satisfy-locality.md). The abstract form is the relational version of the operational one with the store folded into the state; the frame rule's side condition on modified variables then disappears. These properties are the hypotheses of [frame rule soundness is equivalent to safety monotonicity and the frame property](frame-rule-soundness-and-operational-locality.md) and of [the total-correctness frame rule for the heap language](total-correctness-frame-rule-for-heap-language.md) and are recast as one inequality in [local actions correspond to safety-monotone relations with the frame property](local-actions-and-framing-relations.md).

## Sources

- H. Yang and P. O'Hearn, "A semantic basis for local reasoning", *Foundations of Software Science and Computation Structures (FoSSaCS 2002)*, LNCS 2303, Springer, 2002, pp. 402–416, <https://doi.org/10.1007/3-540-45931-6_28>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf>, Section 2, Table 2 (the operational semantics, in which every non-terminal configuration steps or faults), Section 3 (safety and must-termination), Section 4, the statements of Lemmas 1 and 2 and the failing property before Lemma 1, and Section 4.1 (fault trapping and Petri nets with capacity).
- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 3, Conceptual Development (the relational Safety Monotonicity and Frame Property).
