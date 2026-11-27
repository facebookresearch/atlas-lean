# Framed embedding of Hoare validity

Let $P$ and $Q$ be store assertions, $R$ a heap
assertion and $c$ a command of plain IMP, and write $\hat c$ for the embedding of $c$ into heap
IMP. Suppose the partial-correctness Hoare triple with precondition $P$, command $c$ and
postcondition $Q$ is valid, and suppose that whenever $R$ holds of a store $s$ and a heap $h$, it
also holds of $s'$ and $h$ for every store $s'$ that agrees with $s$ on every variable outside the
set of variables that $\hat c$ may assign to. Write $\tilde P$ and $\tilde Q$ for the heap
assertions that hold of a store $s$ and any heap exactly when $P(s)$, respectively $Q(s)$, holds.
Then the separation-logic triple with precondition $\tilde P \star R$, command $\hat c$ and
postcondition $\tilde Q \star R$ is valid, where $\star$ denotes separating conjunction.
