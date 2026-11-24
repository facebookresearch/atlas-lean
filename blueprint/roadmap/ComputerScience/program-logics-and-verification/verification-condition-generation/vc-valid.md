# Verification conditions yield valid Hoare triples

Let $C$ be an annotated command, let
$\mathrm{strip}(C)$ be the IMP command obtained from $C$ by erasing its loop invariants, and let
$P$, $Q$ be assertions. If the verification condition $\mathrm{vc}(C, Q)$ holds and $P$ entails
the precondition $\mathrm{pre}(C, Q)$, then the partial-correctness Hoare triple
$\{P\}\ \mathrm{strip}(C)\ \{Q\}$ is valid.
