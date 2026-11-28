# Soundness of the Iris semantic model

Every entailment derivable in the Iris base logic holds in its step-indexed model: derivability implies semantic entailment between the interpretations, for every assignment of the free variables.

**Theorem (soundness of the semantic model).** If $\Gamma \mid P \vdash Q$ is derivable in the Iris base logic, then for every variable assignment $\rho$ of $\Gamma$, $[\![P]\!]_\rho \models [\![Q]\!]_\rho$ in $\mathrm{UPred}(\mathit{Res})$.

## Depends on

- [Iris base logic](iris-base-logic.md)
- [Uniform predicates](uniform-predicates.md)

## Proof depends on

- [Iris base logic](iris-base-logic.md)
- [Uniform predicates](uniform-predicates.md)
- [Löb induction](lob-induction.md)
- [Guarded fixed points](guarded-fixed-points-of-uniform-predicates.md)
- [Basic update modality](basic-update-modality.md)
- [Cameras](../cameras/cameras.md)

## Expansion

The proof checks each rule of the base logic against the interpretation, after verifying that every connective's interpretation is a uniform predicate and is non-expansive in the assignment. The rules for ownership follow from the camera axioms, UPD-UPDATE from the definition of frame-preserving updates, LÖB by induction on the step index, and the rules for guarded recursion from the fixed-point property; non-expansiveness of function interpretations justifies EQ-LEIBNIZ. The source says the full proof is in its Coq development.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 5, Theorem 3 (soundness of the semantic model), with Figures 10 and 11.
