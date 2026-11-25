# Post-quantum indistinguishability obfuscation from standard assumptions

This node records a research direction: construct general-purpose indistinguishability obfuscation secure against quantum adversaries from well-founded assumptions, ideally from the learning-with-errors assumption alone.

## What would settle it

Assuming a precisely parameterized learning-with-errors problem is hard for quantum polynomial-time algorithms, construct an obfuscator and prove functionality preservation, polynomial slowdown, and indistinguishability of the obfuscations of any two functionally equivalent circuits of the same size against quantum polynomial-time adversaries. The reduction must not rely on an additional unproved obfuscation assumption.

## Status

No cited source poses this question in the form above; it is a research direction motivated by the cited results. This page does not certify the status or novelty of any particular formulation.

Branco, Jain and Srinivasan state that the main pressing question in this area is whether post-quantum indistinguishability obfuscation exists, and that all current lattice-based candidates rely on new, non-standard assumptions, many of which are known to be broken; their result reduces post-quantum obfuscation to obfuscating pseudorandom functions under further assumptions.

This page records a research direction and asserts no theorem or present-status certification.

## Sources

- P. Branco, A. Jain and A. Srinivasan, "Obfuscating pseudorandom functions is post-quantum complete", IACR ePrint 2025/2215, abstract. <https://eprint.iacr.org/2025/2215>
