# Second-order unification with two second-order variables is undecidable

Second-order unification stays undecidable with only two second-order variables and no first-order variables, and with a single second-order variable whose arguments are ground when first-order variables are allowed.

**Theorem (Levy and Veanes).** [Second-order unification](second-order-unification-problems.md), with function variables as the second-order variables and individual variables as the first-order variables, is undecidable for each of the following fragments:

1. problems with two second-order variables and no first-order variables;
2. problems with one second-order variable, applied only to ground arguments, together with first-order variables.

Both are cases of Corollary 16 of the source, which proves undecidability, for some fixed $n$, already for systems in which all arguments of variables are ground terms of depth less than $n$, all variables have arity less than $n$, second-order variables occur at most five times, and either there is a single second-order variable or there are at most two second-order variables and no first-order variables.

Levy and Veanes also translate arbitrary second-order equations into equations with a single second-order variable plus additional first-order variables (Theorem 9 of the source); with Farmer's theorem this gives undecidability with a single unary second-order variable (Corollary 11). So the number of second-order variables plays only a minor role for decidability, as Levy notes. Ganzinger, Jacquemard and Veanes showed undecidability for one second-order variable with at least eight first-order variables. Cerna and Parsert show that associative second-order unification is undecidable already with one second-order variable and no first-order variables.

## Depends on

- [Second-order unification problems](second-order-unification-problems.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Some multi-stack machine has an undecidable halting set](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/exists-not-tm2-decidable-tm2-halts-on.md)

## Expansion

Levy and Veanes prove both fragments in Section 6 of the source by a direct encoding of the halting problem, without Goldfarb's theorem; the paper calls it a simpler proof of Schubert's result. For a fixed deterministic Turing machine $M$ that erases its tape before accepting, two second-order equations $S^M_{sp}(X, F)$ and $S^M_{mv}(F, G)$ are built, using the lemmas of Section 3 on rigid reachability, so that, with $\ulcorner q_0 v_0 \urcorner$ the term representing the initial configuration on input $v_0$, $\{S^M_{sp}(\ulcorner q_0 v_0 \urcorner, F), S^M_{mv}(F, G)\}$ is solvable exactly when $M$ accepts $v_0$ (Theorem 14). Taking for $M$ a universal machine gives a fixed system $S_u(X, F, G)$ of two equations with ground arguments of depth at most $2$ whose solvability for a given ground term is undecidable (Corollary 15), and the transformations of Section 4 then give the fragments (Corollary 16). The reduction needs one fixed machine with an undecidable halting problem. A good expansion links pages for Theorem 14, Corollary 15 and the transformations of Section 4.

## Sources

- J. Levy and M. Veanes, "On the undecidability of second-order unification", *Information and Computation* 159(1–2):125–150, 2000, doi:[10.1006/inco.2000.2877](https://doi.org/10.1006/inco.2000.2877); read in the authors' copy at <https://www.iiia.csic.es/~levy/papers/sou.pdf>, whose numbering is used here: Theorem 9 and Corollary 11 of Section 5, Section 6 with Theorem 14 and Corollaries 15 and 16.
- D. M. Cerna and J. Parsert, "One is all you need: second-order unification without first-order variables", *Logical Methods in Computer Science* 22(2), paper 3, 2026, doi:[10.46298/lmcs-22(2:3)2026](https://doi.org/10.46298/lmcs-22(2:3)2026). Numbering of the version read, arXiv:2404.10616v10: Section 1 (the list of undecidable fragments of second-order unification and the remark on the number of second-order variables).
