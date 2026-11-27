# Bi-abduction

Given symbolic heaps $\Delta$ and $H$, the *bi-abduction* problem asks for symbolic heaps $M$, the *anti-frame*, and $F$, the *frame*, such that

$$\Delta \ast M \vdash H \ast F .$$

Given a frame-inference procedure with $\mathrm{Frame}(H_0, H_1) = L \ne \mathrm{fail} \implies H_0 \vdash H_1 \ast L$ and an abduction procedure with $\mathrm{Abduce}(\Delta, H) = M \ne \mathrm{fail} \implies \Delta \ast M \vdash H$, the algorithm $\mathrm{BiAbd}$ first abduces $M$ for the question $\Delta \ast M \vdash H \ast \mathit{true}$ and then infers the frame $F = \mathrm{Frame}(\Delta \ast M, H)$; whenever it returns $(M, F)$, the entailment $\Delta \ast M \vdash H \ast F$ holds. In compositional program analysis, bi-abduction gives the rule: from a specification $\{A\}\, C\, \{B\}$ and $\mathrm{BiAbd}(P, A) = (M, L)$ infer $\{P \ast M\}\, C\, \{B \ast L\}$, so that the anti-frame is added to the precondition being inferred and the frame is carried across the call.

## Depends on

- [Symbolic heaps with list segments](symbolic-heaps-with-list-segments.md)

## Sources

- C. Calcagno, D. Distefano, P. W. O'Hearn and H. Yang, "Compositional shape analysis by means of bi-abduction", *Journal of the ACM* 58(6), 2011; accepted version (May 2011) <https://www.cs.ox.ac.uk/files/4078/jacm11-biabduction-submitted.pdf>, Section 3.5, Definition 3.26, Theorem 3.27 and the bi-abductive frame rule.
