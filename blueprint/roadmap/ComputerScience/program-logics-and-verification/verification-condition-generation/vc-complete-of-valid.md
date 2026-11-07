# Completeness of verification conditions for valid triples

Let $c$ be an IMP command and
$P$, $Q$ assertions such that the partial-correctness Hoare triple $\{P\}\ c\ \{Q\}$ is valid.
Then there is an annotated command $C$ such that erasing its loop invariants gives $c$, that is
$\mathrm{strip}(C) = c$, the verification condition $\mathrm{vc}(C, Q)$ holds, and $P$ entails
the precondition $\mathrm{pre}(C, Q)$.

The proof goes through relative completeness of the Hoare logic.
