# Guardedness under a prefix flag

For a Boolean flag $b$, recording whether an action
prefix has already been crossed, guardedness of a recursive CCS process under $b$ is defined
recursively: the inactive process $\mathbf{0}$ is guarded under $b$; a constant $A$ is guarded
under $b$ exactly when $b$ is true; a prefix $\alpha.Q$ is guarded under $b$ when $Q$ is guarded
under true; a choice $Q + R$ or a parallel composition $Q \mid R$ is guarded under $b$ when
both $Q$ and $R$ are; and a restriction $Q \setminus L$ or a relabelling $Q[f]$ is guarded
under $b$ when $Q$ is.

Thus under the flag false a process is guarded exactly when every constant occurrence lies
beneath an action prefix. Static operators and parallel/choice contexts do not themselves
guard recursion.
