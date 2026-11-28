# A partial permission cannot guarantee a new value

Over fractional permissions, a command that is safety monotone, termination monotone and framing and never gets stuck cannot both promise in partial correctness that a cell held with a partial permission $z < 1$ ends with a particular different value and be guaranteed to terminate from such a state; executions that change the cell are not excluded.

Work with heaps over the fractional permission model ([fractional and counting permission models](fractional-and-counting-permission-models.md), [permission algebras and heaps with permissions](permission-models.md)). Let $C$ be a command whose executions $C, s, h \leadsto^\ast s', h'$ on these heaps satisfy safety monotonicity, termination monotonicity and the frame property in the operational form of [safety monotonicity and the frame property](../operational-locality/safety-monotonicity-and-the-frame-property.md), and which has progress: no configuration reachable from $C$ is stuck, so every non-terminal configuration either steps or faults. Let $\ell$ be a location, $v \neq v'$ values and $0 < z < 1$. Then $C$ does not satisfy both

1. the fault-avoiding partial-correctness triple $\{\ell \overset{z}{\mapsto} v\}\ C\ \{\ell \overset{z}{\mapsto} v'\}$, meaning that from every state satisfying the precondition $C$ cannot fault and every final state satisfies the postcondition; and
2. $C, s, h$ must terminate normally for some store $s$ and heap $h$ with $s, h \models \ell \overset{z}{\mapsto} v$.

Equivalently, if the triple holds then from every state satisfying its precondition some execution of $C$ diverges: partial correctness alone cannot rule out a command that changes the cell and never terminates. The conclusion concerns a guaranteed new value: the hypotheses do not prevent $C$ from changing the contents of $\ell$ on some terminating executions while leaving them unchanged on others.

## Depends on

- [Fractional and counting permission models](fractional-and-counting-permission-models.md)
- [Permission algebras and heaps with permissions](permission-models.md)
- [Safety monotonicity and the frame property](../operational-locality/safety-monotonicity-and-the-frame-property.md)

## Proof depends on

- [Positivity, disjointness and cross-split](positivity-disjointness-and-cross-split.md)
- [Permission algebras and heaps with permissions](permission-models.md)
- [Fractional and counting permission models](fractional-and-counting-permission-models.md)
- [Frame rule soundness is equivalent to safety monotonicity and the frame property](../operational-locality/frame-rule-soundness-and-operational-locality.md)
- [Splitting and joining fractional points-to assertions](splitting-fractional-points-to-assertions.md)
- [Safety monotonicity and the frame property](../operational-locality/safety-monotonicity-and-the-frame-property.md)

## Expansion

Suppose both hold. Heaps over fractional permissions form a separation algebra, since $(0, 1]$ is the set of non-unit fractional shares and the fractional shares are positive, so no two non-units join to the unit. Fix the store $s$; the frame $r = \ell \overset{1-z}{\mapsto} v$ mentions no variable, so the frame rule for the relation of $C$ on heaps at $s$, valid by safety monotonicity and the frame property, gives $\{\ell \overset{z}{\mapsto} v \ast \ell \overset{1-z}{\mapsto} v\}\ C\ \{\ell \overset{z}{\mapsto} v' \ast \ell \overset{1-z}{\mapsto} v\}$. Its postcondition is unsatisfiable, because the two halves disagree on the contents of $\ell$. The heap $h \circ [\ell \mapsto (v, 1 - z)] = [\ell \mapsto (v, 1)]$ is defined, so by termination monotonicity $C$ must terminate normally from it; since no reachable configuration is stuck, every maximal execution from it is finite and ends in a terminal state. By the framed triple, that terminal state satisfies an unsatisfiable postcondition, a contradiction. Commands of the permission-checked heap language have progress, since in its semantics every non-terminal configuration steps or faults. Without progress the statement fails: a command that faults when $\ell$ is absent or held with permission below $1/2$, steps from exactly $[\ell \mapsto (v, 1/2)]$ to the terminal state $[\ell \mapsto (v', 1/2)]$ and has no step from any other safe heap satisfies the three locality properties, the triple and must-termination, because its stuck configurations count as terminating. The permission-accounting paper gives the argument for $z = 1/2$, for a triple promising a particular different final value under must-termination, and asserts that the commands of its sequential language satisfy the three locality properties over permission heaps; a page proving that assertion would discharge the hypothesis for every command of that language. The conclusion depends on the sequential setting: a command that can acquire permission from a shared resource, such as a conditional critical region whose invariant holds the other half of the permission, can change the cell, and the framed triple is then vacuous rather than contradictory.

## Sources

- R. Bornat, C. Calcagno, P. O'Hearn and M. Parkinson, "Permission accounting in separation logic", *Proceedings of the 32nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2005)*, ACM, 2005, pp. 259–270, <https://doi.org/10.1145/1040305.1040327>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/permissions_paper.pdf>, Section 7.1 (the passivity argument with permission $0.5$ and the example with a resource bundle) and Section 11.3 (safety monotonicity, termination monotonicity and the frame property for permission heaps).
- H. Yang and P. O'Hearn, "A semantic basis for local reasoning", *Foundations of Software Science and Computation Structures (FoSSaCS 2002)*, LNCS 2303, Springer, 2002, pp. 402–416, <https://doi.org/10.1007/3-540-45931-6_28>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf>, Section 3 (partial and total correctness) and Section 4, Lemma 1 (termination monotonicity).
