# Extended resolution and extended Frege are p-equivalent

Extended resolution and extended Frege polynomially simulate each other. Repeated clausal extensions build any Boolean circuit, which lets extended resolution mimic the general extension rule of extended Frege, while extended Frege simulates resolution and its extension clauses directly.

**Theorem.** [Extended resolution](../../../propositional-logic/sat-solving/extended-resolution.md) and extended Frege p-simulate each other, where formulas are compared through the standard translation: a formula $\varphi$ is turned into a CNF that is unsatisfiable iff $\varphi$ is a tautology, by adding a new variable $x_A$ for each subformula $A$, clauses stating that each $x_A$ is computed correctly from its immediate subformulas, and the unit clause $\neg x_\varphi$.

In particular, a family of tautologies has polynomial-size extended Frege proofs if and only if the corresponding CNFs have polynomial-size extended resolution refutations.

## Expansion

Extended resolution is taken as on [its page](../../../propositional-logic/sat-solving/extended-resolution.md), whose extensions introduce definitions $x\leftrightarrow p\vee(c_1\wedge\dots\wedge c_k)$. Buss and Nordström state the clausal rule (7.70) as the three clauses $\neg x\vee a$, $\neg x\vee b$, $\neg a\vee\neg b\vee x$ for $x\leftrightarrow(a\wedge b)$, with $x$ a new variable, which in particular does not occur in $a$ or $b$. Up to writing the fresh literal $y$ as $\neg x$, these are the clauses of Tseitin's original definition $y\leftrightarrow\bar a\vee\bar b$ recorded on that page; the two presentations take different extension instructions as primitive.

From extended Frege to extended resolution: the general extension rule $x\leftrightarrow\varphi$ is simulated by introducing one clausal extension variable for each gate of $\varphi$; once every line of the Frege proof is represented by an extension variable, each Frege inference becomes a constant number of resolution steps on these variables. In the circuit view, extended Frege is $\mathsf{P/poly}$-Frege, and extended resolution can generate any polynomial-size circuit with polynomially many extensions. From extended resolution to extended Frege: resolution steps are Frege inferences on clauses, and the extension clauses follow from an extension line for the same definition. The formula-to-CNF translation in the statement is a form of the [Tseitin transformation](../../../propositional-logic/tseitin-transformation/tseitin.md).

Resolution does not p-simulate extended resolution: the pigeonhole formulas have polynomial-size extended resolution refutations (Cook and Reckhow) but require exponential-size resolution refutations ([Haken](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)). In SAT solving the extension clauses can be added one at a time as RAT clauses, and conversely [extended resolution polynomially simulates DRAT](../../../propositional-logic/sat-solving/extended-resolution-simulates-drat.md).

## Depends on

- [Extended Frege proof systems](extended-frege-system.md)
- [Extended resolution](../../../propositional-logic/sat-solving/extended-resolution.md)

## Proof depends on

None.

## Sources

- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.8: the general extension rule (7.69), the clausal extension rule (7.70) expressing $x\leftrightarrow(a\wedge b)$, using (7.70) repeatedly to simulate (7.69), so extended resolution simulates and is simulated by extended Frege, and the exponential separation from resolution via the pigeonhole principle; Section 7.9: extended Frege is equivalent to extended resolution).
- Paul Beame and Toniann Pitassi, "Propositional proof complexity: past, present, and future", *Bulletin of the EATCS* 65, 1998; reprinted in *Current Trends in Theoretical Computer Science*, World Scientific, 2001; ECCC report TR98-067, <https://eccc.weizmann.ac.il/report/1998/067/> (Section 2.2: the translation of formulas into CNFs with subformula variables; Section 2.3: extended resolution is p-equivalent to extended Frege because it can generate any $\mathsf{P/poly}$ circuit with polynomially many extensions).
