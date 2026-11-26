# Weak and strong fairness

Let $\sigma$ be a labeled infinite execution and $A$ a class of labels. The class is enabled at a state when at least one outgoing transition has a label in $A$. The witness label and target may vary at different states. An occurrence, by contrast, uses the label actually taken by $\sigma$ at that step.

- **Weak fairness:** if $A$ is enabled at every state from some index onward, the execution takes labels in $A$ infinitely often.
- **Strong fairness:** if $A$ is enabled at arbitrarily late states, the execution takes labels in $A$ infinitely often.

Strong fairness implies weak fairness, since eventual permanent enabledness implies arbitrarily late enabledness. The converse fails: an execution can visit an enabling and a disabling state alternately without ever taking a label in the class. It is then weakly fair, since there is no permanently enabling suffix, but not strongly fair.

## Background

An [infinite state run](../../process-calculi/labelled-transition-systems/omega-run.md) requires some transition at every step but need not specify which label was taken. That information is retained in the labeled execution used here.

In Fischer, Lynch, and Paterson's model, a nonfaulty process takes infinitely many steps. Admissibility separately requires that at most one process is faulty and that every message sent to a nonfaulty process is eventually received. Those delivery and failure conditions are not the action-class predicates defined here.

## Sources

- L. Lamport, "The temporal logic of actions", *ACM Transactions on Programming Languages and Systems* 16(3):872–923, 1994, Section 5.3 (weak fairness $\Box(\Diamond \text{executed} \lor \Diamond \text{impossible})$ and strong fairness $\Box(\Diamond \text{executed} \lor \Diamond\Box \text{impossible})$, which for an infinite execution are equivalent to the definitions above)
- M. J. Fischer, N. A. Lynch and M. S. Paterson, "Impossibility of distributed consensus with one faulty process", *Journal of the ACM* 32(2):374–382, 1985, Section 2
