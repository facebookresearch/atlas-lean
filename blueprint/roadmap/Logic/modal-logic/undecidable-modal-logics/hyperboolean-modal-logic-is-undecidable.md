# Hyperboolean modal logic is undecidable

Hyperboolean modal logic, the modal logic of Boolean algebras viewed as frames with modalities for their operations, is undecidable, already in its fragment with only the binary diamond for join.

**Theorem (Knudstorp).** Let $\mathsf{BA}_\vee$ be the class of frames $(B, \vee)$ given by the join-reducts of Boolean algebras $(B, \vee, \wedge, \neg, \bot, \top)$, each read as an [associative frame](associative-normal-modal-logic.md) with $Rxyz$ iff $x = y \vee z$. The logic $\mathrm{Log}(\mathsf{BA}_\vee)$ of $\mathcal L$-formulas valid on all these frames is undecidable. Consequently hyperboolean modal logic (Goranko and Vakarelov), whose fragment in the single binary modality $\langle\vee\rangle$ is $\mathrm{Log}(\mathsf{BA}_\vee)$, is undecidable. The same argument applies with $\langle\wedge\rangle$ in place of $\langle\vee\rangle$.

This answers the question of decidability of hyperboolean modal logic posed by Goranko and Vakarelov.

## Depends on

- [Associative normal modal logic](associative-normal-modal-logic.md)
- [Boolean algebra](../../../Order/lattices-boolean-algebras/boolean-algebra.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Associative modal logics valid on the union frame are undecidable](associative-modal-logics-below-the-union-frame.md)

## Expansion

Joins in a Boolean algebra are associative, so every frame in $\mathsf{BA}_\vee$ is associative and $\mathbf{AK}_2 \subseteq \mathrm{Log}(\mathsf{BA}_\vee)$. The powerset $\mathcal P(\mathbb N)$ is a Boolean algebra, so $(\mathcal P(\mathbb N), \cup) \in \mathsf{BA}_\vee$ and $\mathrm{Log}(\mathsf{BA}_\vee) \subseteq \mathrm{Log}(\mathcal P(\mathbb N), \cup)$. The theorem on associative logics below the union frame applies; undecidability of a fragment in a subsignature implies undecidability of the full logic.

## Sources

- S. B. Knudstorp, "Diamonds and dominoes: impossibility results for associative modal logics", *The Journal of Symbolic Logic*, published online 2026, pp. 1–26, <https://doi.org/10.1017/jsl.2026.10256>; numbers from arXiv:2506.16366v2, <https://arxiv.org/abs/2506.16366v2>: Theorem 3.6 and its proof.
- V. Goranko and D. Vakarelov, "Hyperboolean algebras and hyperboolean modal logic", *Journal of Applied Non-Classical Logics* 9(2–3):345–368, 1999, <https://doi.org/10.1080/11663081.1999.10510971>: the logic and the decidability question; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Section 1, Section 2 and the proof of Theorem 3.6).
