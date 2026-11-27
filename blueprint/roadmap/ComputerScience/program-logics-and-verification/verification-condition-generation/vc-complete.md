# Completeness of verification conditions for derivable triples

Let $c$ be an IMP command
and $P$, $Q$ assertions such that the Hoare triple $\{P\}\ c\ \{Q\}$ is derivable in the
partial-correctness Hoare logic. Then there is an annotated command $C$ such that erasing its
loop invariants gives $c$, that is $\mathrm{strip}(C) = c$, the verification condition
$\mathrm{vc}(C, Q)$ holds, and $P$ entails the precondition $\mathrm{pre}(C, Q)$.

Compiled reading: the same annotated command $C$ gives a [compiled annotation](../compiling-imp-verification-conditions-into-diagr/annotate.md) $\mathrm{annotate}(C, Q)$ of the compiled diagram of $c$ whose diagram obligations from the $P$-states to the $Q$-states hold, since by [the equivalence of those obligations with the source conditions](../compiling-imp-verification-conditions-into-diagr/vc-annotate-iff.md) they hold exactly when $P$ entails $\mathrm{pre}(C, Q)$ and $\mathrm{vc}(C, Q)$ holds.
