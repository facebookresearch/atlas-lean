# Extended resolution and extended Frege are p-equivalent

Extended resolution and extended Frege polynomially simulate each other. Repeated clausal extensions build any Boolean circuit, which lets extended resolution mimic the general extension rule of extended Frege, while extended Frege simulates resolution and its extension clauses directly.

**Theorem.** Extended resolution and extended Frege p-simulate each other, where formulas are compared through the standard translation: a formula $\varphi$ is turned into a CNF that is unsatisfiable iff $\varphi$ is a tautology, by adding a new variable $x_A$ for each subformula $A$, clauses stating that each $x_A$ is computed correctly from its immediate subformulas, and the unit clause $\neg x_\varphi$.

In particular, a family of tautologies has polynomial-size extended Frege proofs if and only if the corresponding CNFs have polynomial-size extended resolution refutations.

## Expansion

From extended Frege to extended resolution: the general extension rule $x\leftrightarrow\varphi$ is simulated by introducing one clausal extension variable for each gate of $\varphi$, using the rule $x\leftrightarrow(a\wedge b)$ together with negated literals; once every line of the Frege proof is represented by an extension variable, each Frege inference becomes a constant number of resolution steps on these variables. In the circuit view, extended Frege is $\mathsf{P/poly}$-Frege, and extended resolution can generate any polynomial-size circuit with polynomially many extensions. From extended resolution to extended Frege: resolution steps are Frege inferences on clauses, and the three extension clauses follow from an extension line $x\leftrightarrow(a\wedge b)$.

## Depends on

- [Extended Frege proof systems](extended-frege-system.md)
- [Extended resolution](extended-resolution.md)

## Proof depends on

None.

## Sources

- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.8: using the clausal extension rule (7.70) repeatedly simulates the full extension rule (7.69), so extended resolution simulates and is simulated by extended Frege; Section 7.9: extended Frege is equivalent to extended resolution).
- Paul Beame and Toniann Pitassi, "Propositional proof complexity: past, present, and future", *Bulletin of the EATCS* 65, 1998; reprinted in *Current Trends in Theoretical Computer Science*, World Scientific, 2001, <https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2014W/BeamePitassi_pastpresentfuture.pdf> (Section 2.2: the translation of formulas into CNFs with subformula variables; Section 2.3: extended resolution is p-equivalent to extended Frege because it can generate any $\mathsf{P/poly}$ circuit with polynomially many extensions).
