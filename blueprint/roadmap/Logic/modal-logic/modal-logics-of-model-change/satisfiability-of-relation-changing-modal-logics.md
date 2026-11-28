# Satisfiability of relation-changing modal logics is undecidable

The satisfiability problem is undecidable for each of the six relation-changing modal logics obtained by adding to the basic modal language a local or global sabotage, bridge or swap operator.

**Theorem (Löding and Rohde; Areces, Fervari and Hoffmann; Fervari; Martel).** For each $\blacklozenge \in \{\langle sb\rangle, \langle br\rangle, \langle sw\rangle, \langle gsb\rangle, \langle gbr\rangle, \langle gsw\rangle\}$, the satisfiability problem of the [relation-changing modal logic](relation-changing-modal-logics.md) $\mathcal{ML}(\blacklozenge)$ is undecidable.

The survey statement read is the one of Areces, Fervari, Hoffmann and Martel, who recall it as known with these four sources and use translations into hybrid logic to identify decidable fragments. The cited sources include the paper of Löding and Rohde on satisfiability for sabotage modal logic and the paper of Areces, Fervari and Hoffmann on swap logic, which studies the decidability of local swap logic. Satisfiability of the basic modal logic itself is decidable; the operators that change the model are what make these logics undecidable.

## Depends on

- [Relation-changing modal logics](relation-changing-modal-logics.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The six logics translate into the hybrid logic $\mathcal{HL}(\mathsf E, \downarrow)$ with the universal modality and the down-arrow binder, some of them into $\mathcal{HL}(:, \downarrow)$, which is a reduction class of first-order logic; the undecidability proofs themselves are in the cited sources and are not reproduced in the survey read. A good expansion states the reduction used for each operator and links the undecidable problem it starts from.

## Sources

- C. Areces, R. Fervari, G. Hoffmann and M. Martel, "Relation-changing logics as fragments of hybrid logics", in *Proceedings of the Seventh International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2016)*, Electronic Proceedings in Theoretical Computer Science 226, 2016, pp. 16–29, <https://doi.org/10.4204/EPTCS.226.2>; read as arXiv:1609.04086v1, <https://arxiv.org/abs/1609.04086v1>: Section 1 (the statement, with references [7], [16], [21] and [22] of that version), Sections 3 and 4.
- C. Löding and P. Rohde, "Model checking and satisfiability for sabotage modal logic", in *FST TCS 2003*, Lecture Notes in Computer Science 2914, Springer, 2003, pp. 302–313, <https://doi.org/10.1007/978-3-540-24597-1_26>; cited beside the copy read.
- C. Areces, R. Fervari and G. Hoffmann, "Swap logic", *Logic Journal of the IGPL* 22(2):309–332, 2014, <https://doi.org/10.1093/jigpal/jzt030>; cited beside the copy read.
- R. Fervari, *Relation-Changing Modal Logics*, PhD thesis, Universidad Nacional de Córdoba, 2014; and M. Martel, *On the Undecidability of Relation-Changing Logics*, Master's thesis, Universidad Nacional de Río Cuarto, 2015; both cited beside the copy read.
