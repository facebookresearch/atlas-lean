# Verification conditions yield valid Hoare triples

Let $C$ be an annotated command, let
$\mathrm{strip}(C)$ be the IMP command obtained from $C$ by erasing its loop invariants, and let
$P$, $Q$ be assertions. If the verification condition $\mathrm{vc}(C, Q)$ holds and $P$ entails
the precondition $\mathrm{pre}(C, Q)$, then the partial-correctness Hoare triple
$\{P\}\ \mathrm{strip}(C)\ \{Q\}$ is valid.

Compiled reading: under the same hypotheses, the compiled diagram of $\mathrm{strip}(C)$ has a traced Hoare derivation from the $P$-states to the $Q$-states. The two conclusions are equivalent, because derivability of the compiled diagram is derivability of the source triple, which is its validity by soundness and relative completeness of Hoare logic.
