# Satisfiability of spatial multi-lane spatial logic is undecidable

Whether a formula of the spatial fragment of multi-lane spatial logic holds for some traffic snapshot, view and valuation is undecidable, even when only the length of views, not their width, is used.

**Theorem (Linker and Hilscher).** The satisfiability problem of spatial [MLSL](multi-lane-spatial-logic.md) is undecidable: there is no algorithm that decides, given a formula built from $\bot$, equations between terms, the atoms $\mathit{re}(c)$ and $\mathit{cl}(c)$, implication, quantification and the horizontal and vertical chop operators, whether some traffic snapshot $TS$, view $V$ and valuation $\nu$ satisfy it.

The source remarks that the proof goes through without the width term $\omega$, so the fragment using only the length term $\ell$ is already undecidable. The extension EMLSL with modalities for snapshot transitions is therefore undecidable too, which is why the source turns to a sound (labelled natural deduction) proof system rather than a decision procedure.

## Depends on

- [Multi-lane spatial logic](multi-lane-spatial-logic.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for two-counter machines (Minsky): is there a run from $(q_0, 0, 0)$ reaching the final state $q_{\mathrm{fin}}$? Following the encoding of Zhou, Hansen and Sestoft for Duration Calculus, configurations are laid out horizontally as consecutive segments of length $4k$, made of the control state, the first counter, a delimiter and the second counter, each of length $k$. Since spatial MLSL has only the predicates for reservations and claims (and the derived free space), states, counter units and delimiters are encoded by patterns of reserved, claimed and free space; the sanity conditions on snapshots rule out using several reservations of a single car to stand for, say, the units of a counter, so the encoding is spread over many cars. Formulas force the initial configuration, the correct effect of each increment and decrement instruction between consecutive configurations, and the eventual occurrence of $q_{\mathrm{fin}}$, so the formula is satisfiable iff the machine has a halting run (Proposition 3.1).

## Sources

- S. Linker and M. Hilscher, "Proof Theory of a Multi-Lane Spatial Logic", *Logical Methods in Computer Science* 11(3), 2015, paper 4, <https://doi.org/10.2168/LMCS-11(3:4)2015>; numbers from arXiv:1504.06986v2, <https://arxiv.org/abs/1504.06986v2>: Section 3: Proposition 3.1 and Theorem 3.2, with the remark following it.
- C. Zhou, M. R. Hansen and P. Sestoft, "Decidability and undecidability results for duration calculus", in *STACS 93*, Lecture Notes in Computer Science 665, Springer, 1993, pp. 58–68, <https://doi.org/10.1007/3-540-56503-5_8>: the encoding of two-counter machines adapted in the proof; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Section 3).
