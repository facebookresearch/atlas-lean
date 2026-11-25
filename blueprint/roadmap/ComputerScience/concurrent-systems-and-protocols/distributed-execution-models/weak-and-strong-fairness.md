# Weak and strong fairness

Let $\sigma$ be an infinite execution and $A$ a class of actions. Say that $A$ is enabled in a state if some action of $A$ is enabled there. $\sigma$ is *weakly fair* for $A$ if, whenever $A$ is enabled in every state from some point on, actions of $A$ occur infinitely often in $\sigma$; it is *strongly fair* for $A$ if, whenever $A$ is enabled in infinitely many states of $\sigma$, actions of $A$ occur infinitely often. Enabledness of the class need not be witnessed by one fixed action. In the model of Fischer, Lynch and Paterson, a process is *nonfaulty* in a run if it takes infinitely many steps, and a run is *admissible* if at most one process is faulty and every message sent to a nonfaulty process is eventually received; eventual receipt is the fairness component, and the bound of one faulty process is part of the failure model.

## Depends on

- [Infinite run](../../process-calculi/labelled-transition-systems/omega-run.md)

## Sources

- L. Lamport, "The temporal logic of actions", *ACM Transactions on Programming Languages and Systems* 16(3):872–923, 1994, Section 5.3 (weak fairness $\Box(\Diamond \text{executed} \lor \Diamond \text{impossible})$ and strong fairness $\Box(\Diamond \text{executed} \lor \Diamond\Box \text{impossible})$, which for an infinite execution are equivalent to the definitions above)
- M. J. Fischer, N. A. Lynch and M. S. Paterson, "Impossibility of distributed consensus with one faulty process", *Journal of the ACM* 32(2):374–382, 1985, Section 2
