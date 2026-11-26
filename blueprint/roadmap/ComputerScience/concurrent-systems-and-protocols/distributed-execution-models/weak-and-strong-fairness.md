# Weak and strong fairness

Let $\sigma$ be a labeled infinite execution and $C$ a class of labels. The class is enabled at a state when at least one outgoing transition has a label in $C$. The witness label and target may vary at different states. An occurrence, by contrast, uses the label actually taken by $\sigma$ at that step.

- **Weak fairness:** if $C$ is enabled at every state from some index onward, the execution takes labels in $C$ infinitely often.
- **Strong fairness:** if $C$ is enabled at arbitrarily late states, the execution takes labels in $C$ infinitely often.

Strong fairness implies weak fairness, since eventual permanent enabledness implies arbitrarily late enabledness. The converse fails: an execution can visit an enabling and a disabling state alternately without ever taking a label in the class. It is then weakly fair, since there is no permanently enabling suffix, but not strongly fair.

## Background

An [infinite state run](../../process-calculi/labelled-transition-systems/omega-run.md) requires some transition at every step but need not specify which label was taken. That information is retained in the labeled execution used here.

Lamport's $\mathrm{WF}_f(A)$ and $\mathrm{SF}_f(A)$ concern $\langle A \rangle_f = A \wedge f' \ne f$, the steps of action $A$ that change the value of the state function $f$. Equations (17) and (18) give the weak and strong fairness conditions above on an infinite execution when both tests agree:

- The label taken at a step belongs to $C$ exactly when the step satisfies $\langle A \rangle_f$.
- At each state $s$ of the execution, an outgoing transition with a label in $C$ exists exactly when there is a target state $t$ in the TLA state space with $A(s,t)$ and $f(t) \ne f(s)$.

Stuttering steps are allowed in the execution, but steps that leave $f$ unchanged do not count as occurrences or witnesses of enabledness for Lamport's conditions. For example, take $f$ to be the identity and let $A$ consist of $s \to s$ and $s \to t$ with $t \ne s$. Give both transitions the same label in $C$. An execution can stay at $s$ forever and take a label in $C$ every time, satisfying both label-based conditions. The exit to $t$ makes $\langle A \rangle_f$ continuously enabled, but no such step occurs, so neither of Lamport's conditions holds.

In Fischer, Lynch, and Paterson's model, a nonfaulty process takes infinitely many steps. Admissibility separately requires that at most one process is faulty and that every message sent to a nonfaulty process is eventually received. Those delivery and failure conditions are not the action-class predicates defined here.

## Sources

- L. Lamport, "The temporal logic of actions", *ACM Transactions on Programming Languages and Systems* 16(3):872–923, 1994, Section 5.3, equations (17) and (18), <https://lamport.azurewebsites.net/pubs/lamport-actions.pdf>
- M. J. Fischer, N. A. Lynch and M. S. Paterson, "Impossibility of distributed consensus with one faulty process", *Journal of the ACM* 32(2):374–382, 1985, Section 2
