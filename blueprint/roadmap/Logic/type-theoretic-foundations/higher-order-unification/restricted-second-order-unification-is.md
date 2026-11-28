# Second-order unification with two second-order variables is undecidable

Second-order unification stays undecidable with only two second-order variables and no first-order variables, and with a single second-order variable whose arguments are ground when first-order variables are allowed.

**Theorem (Levy and Veanes).** [Second-order unification](second-order-unification-problems.md), with function variables as the second-order variables and individual variables as the first-order variables, is undecidable for each of the following fragments:

1. problems with two second-order variables and no first-order variables;
2. problems with one second-order variable, applied only to ground arguments, together with first-order variables.

Levy and Veanes also translate arbitrary second-order equations into equations with a single second-order variable plus additional first-order variables. So the number of second-order variables plays only a minor role for decidability, as Levy notes. Ganzinger, Jacquemard and Veanes showed undecidability for one second-order variable with at least eight first-order variables. Cerna and Parsert show that associative second-order unification is undecidable already with one second-order variable and no first-order variables.

## Depends on

- [Second-order unification problems](second-order-unification-problems.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Second-order unification is undecidable](second-order-unification-is-undecidable.md)

## Expansion

Levy and Veanes obtain the fragments by translating general second-order unification problems, undecidable by Goldfarb's theorem, into problems with fewer variables of the stated kinds while preserving solvability.

## Sources

- J. Levy and M. Veanes, "On the undecidability of second-order unification", *Information and Computation* 159(1–2):125–150, 2000, doi:[10.1006/inco.2000.2877](https://doi.org/10.1006/inco.2000.2877) (original source, cited beside the copy read).
- D. M. Cerna and J. Parsert, "One is all you need: second-order unification without first-order variables", *Logical Methods in Computer Science* 22(2), paper 3, 2026, doi:[10.46298/lmcs-22(2:3)2026](https://doi.org/10.46298/lmcs-22(2:3)2026). Numbering of the version read, arXiv:2404.10616v10: Section 1 (the list of undecidable fragments of second-order unification and the remark on the number of second-order variables).
