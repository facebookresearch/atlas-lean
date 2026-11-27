# Soundness of RC for RC-models

If $A \vdash B$ is derivable in RC, then $A \vdash B$ is true in every Kripke model on an
RC-frame.

Proof: induction on the derivation. Axiom 3 and axioms 4 follow from polytransitivity, axiom 5
from condition (J) and axiom 6 from monotonicity.

## Background

- [The Reflection Calculus RC](derives.md)
- [RC-frame](is-frame.md)
- [Truth of a strictly positive formula in a Kripke model](satisfies.md)

## Sources

- L. D. Beklemishev, "Positive provability logic for uniform reflection principles", arXiv:1304.4396v3 (2013), *Annals of Pure and Applied Logic* 165 (2014), Lemma 4.2(ii).
