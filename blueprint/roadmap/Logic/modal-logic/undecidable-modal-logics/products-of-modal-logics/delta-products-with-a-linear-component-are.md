# δ-products with a linear component are undecidable

The δ-product of a logic of linear orders validated by $(\omega,<)$ with any Kripke complete logic having an infinite fan among its frames is undecidable; in particular $\mathbf{K4.3} \times^\delta \mathbf{S5}$ and $\mathbf{K4.3} \times^\delta \mathbf{K}$ are undecidable.

**Theorem (Hampson, Kikot and Kurucz).** Let $L_h$ be a Kripke complete unimodal logic containing $\mathbf{K4.3}$ such that $(\omega,<)$ is a frame for $L_h$, and let $L_v$ be a Kripke complete unimodal logic such that some $\omega$-fan is a frame for $L_v$. Then the [δ-product](delta-products-of-modal-logics.md) $L_h \times^\delta L_v$ is undecidable (Theorem 4). In particular $\mathbf{K4.3} \times^\delta \mathbf{S5}$ and $\mathbf{K4.3} \times^\delta \mathbf{K}$ are undecidable (Corollary 3).

Here $\mathbf{K4.3}$ is the unimodal logic of linear orders, whose frames are the transitive, weakly connected frames; undecidability refers to the validity problem. Without the diagonal, $\mathbf{K4.3} \times \mathbf{S5}$ is decidable in 2EXPTIME.

## Depends on

- [Delta-products of modal logics](delta-products-of-modal-logics.md)
- [Extra axioms of S5](../../normal-modal-logics/s5.md)
- [Extra axioms of the modal logic K](../../normal-modal-logics/k.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

As for a $\mathbf{K}$ component, the proof reduces non-termination of counter machines to satisfiability: a formula generates an $\omega \times \omega$ grid whose horizontal coordinates form an increasing chain in the linear component, and encodes simultaneously a lossy and an incrementing-error run of the same instruction sequence, which together yield a reliable non-terminating run (Section 6).

## Sources

- Christopher Hampson, Stanislav Kikot and Agi Kurucz, "The decision problem of modal product logics with a diagonal, and faulty counter machines", *Studia Logica* 104(3):455–486, 2016, doi:10.1007/s11225-015-9647-7; read as arXiv:1509.02060v1, <https://arxiv.org/abs/1509.02060v1>: Theorem 4, Corollary 3 and Section 6 of arXiv:1509.02060v1.
