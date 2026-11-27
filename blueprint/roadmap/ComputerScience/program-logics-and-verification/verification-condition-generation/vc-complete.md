# Completeness of verification conditions for derivable triples

Let $c$ be an IMP command
and $P$, $Q$ assertions such that the Hoare triple $\{P\}\ c\ \{Q\}$ is derivable in the
partial-correctness Hoare logic. Then there is an annotated command $C$ such that erasing its
loop invariants gives $c$, that is $\mathrm{strip}(C) = c$, the verification condition
$\mathrm{vc}(C, Q)$ holds, and $P$ entails the precondition $\mathrm{pre}(C, Q)$.
