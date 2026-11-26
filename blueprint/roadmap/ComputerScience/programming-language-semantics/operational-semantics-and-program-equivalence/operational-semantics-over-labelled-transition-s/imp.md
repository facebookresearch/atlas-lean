# Operational semantics of IMP

The operational semantics of IMP is the instance of an [operational semantics](op-sem.md) whose configurations are IMP configurations, pairs of a command and a state, and whose labels are the one-element type. A step from one configuration to another, with the unique label, is exactly an IMP [small step](../../operational-semantics-of-imp/step.md), and a configuration $(\mathit{cmd}, s)$ is final exactly when $\mathit{cmd} = \mathtt{skip}$. Final configurations are terminal, since $\mathtt{skip}$ takes no small step.
