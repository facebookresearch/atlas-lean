# Soundness and relative completeness of partial-correctness Hoare logic

For all assertions $P$ and $Q$ and every command $c$, the triple $\{P\}\,c\,\{Q\}$ is derivable in
partial-correctness Hoare logic if and only if it is valid for partial correctness.

In the [categorical reading](../imp-hoare-logic-through-categorical-verification/triple-iff-valid.md), where a command denotes its execution relation in the relation category of states and a triple is checked by powerset verification, validity of $\{P\}\,c\,\{Q\}$ is the categorical triple for the same $P$, $c$ and $Q$, so derivability is also exactly the categorical triple.
