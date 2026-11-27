# Frame rule

Let $P$, $Q$ and $R$ be heap assertions and $c$ a heap command. Suppose the
separation-logic triple with precondition $P$, command $c$ and postcondition $Q$ is valid, and
suppose that whenever $R$ holds of a store $s$ and a heap $h$, it also holds of $s'$ and $h$ for
every store $s'$ that agrees with $s$ on every variable outside the set of variables that $c$ may
assign to. Then the triple with precondition $P \star R$, command $c$ and postcondition
$Q \star R$ is valid, where $\star$ denotes separating conjunction.

In terms of the [safe backward precondition](../separating-implication-and-safe-backward-precond/safe-pre.md), the triple with precondition $P$ is valid exactly when $P$ entails the safe precondition of $c$ and $Q$, so the rule has two equivalent pointwise readings for the same side condition on $R$: the safe precondition of $c$ and $Q$, separated from $R$, entails the safe precondition of $c$ and $Q \star R$; and, by the [adjunction between separating conjunction and separating implication](../separating-implication-and-safe-backward-precond/star-entails-iff-entails-wand.md), the safe precondition of $c$ and $Q$ entails $R$ separately implying the safe precondition of $c$ and $Q \star R$. The first is the rule with $P$ the safe precondition of $c$ and $Q$; conversely, for every precondition $P$ that entails the safe precondition of $c$ and $Q$, framing that entailment gives that $P \star R$ entails the safe precondition of $c$ and $Q$, separated from $R$, and the first reading then gives the rule.
