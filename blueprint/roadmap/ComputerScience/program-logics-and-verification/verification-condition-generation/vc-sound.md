# Soundness of verification conditions

For an annotated command $C$ and an assertion $Q$,
write $\mathrm{pre}(C, Q)$ and $\mathrm{vc}(C, Q)$ for the precondition and the verification
condition of $C$ for the postcondition $Q$, and $\mathrm{strip}(C)$ for the IMP command obtained
from $C$ by erasing its loop invariants. For every such $C$ and $Q$, if $\mathrm{vc}(C, Q)$
holds, then the Hoare triple $\{\mathrm{pre}(C, Q)\}\ \mathrm{strip}(C)\ \{Q\}$ is derivable in
the partial-correctness Hoare logic.
