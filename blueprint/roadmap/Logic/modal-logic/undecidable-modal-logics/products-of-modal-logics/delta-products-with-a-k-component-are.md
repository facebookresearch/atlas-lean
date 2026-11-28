# δ-products with a K component are undecidable

Adding the diagonal constant to the product of the basic modal logic K with any Kripke complete logic that has an infinite fan among its frames yields an undecidable logic; in particular $\mathbf{K} \times^\delta \mathbf{S5}$ is undecidable, although $\mathbf{K} \times \mathbf{S5}$ is coNEXPTIME-complete.

**Theorem (Hampson, Kikot and Kurucz).** Let $L$ be any Kripke complete unimodal logic such that some $\omega$-fan is a frame for $L$. Then the [δ-product](delta-products-of-modal-logics.md) $\mathbf{K} \times^\delta L$ is undecidable (Theorem 2). In particular $\mathbf{K} \times^\delta \mathbf{S5}$ is undecidable (Corollary 2).

Here $\mathbf{K}$ is the logic of all frames and is the horizontal component, $L$ is the vertical component, and undecidability refers to the validity problem with the formula as input. The source also proves that $\mathbf{K} \times^\delta \mathbf{K}$ and $\mathbf{K} \times^\delta \mathbf{K4}$ are undecidable (Corollary 1), by a separate reduction from global consequence in the products $\mathbf{K} \times \mathbf{K}$ and $\mathbf{K} \times \mathbf{K4}$.

## Depends on

- [Delta-products of modal logics](delta-products-of-modal-logics.md)
- [Extra axioms of the modal logic K](../../normal-modal-logics/k.md)
- [Extra axioms of S5](../../normal-modal-logics/s5.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from non-termination of counter machines ($\Pi^0_1$-hard) to satisfiability. A formula forces an $\omega \times \omega$ grid in any model on a δ-product frame, using the uniqueness of the diagonal point in each row and each column. The formalism cannot force reliable counter updates directly, but it can encode, for the same instruction sequence, a *lossy* run (counters may spontaneously decrease) and an *incrementing-error* run (counters may spontaneously increase, decrements happening only at diagonal points). From such a pair of faulty runs one reconstructs a reliable infinite run; conversely, a non-terminating machine yields a model on $\mathfrak{H}_\omega \times^\delta \mathfrak{F}$ for an $\omega$-fan $\mathfrak{F}$. By contrast, $\mathbf{K} \times^\delta \mathbf{Alt}(n)$ is decidable (Theorem 6).

## Sources

- Christopher Hampson, Stanislav Kikot and Agi Kurucz, "The decision problem of modal product logics with a diagonal, and faulty counter machines", *Studia Logica* 104(3):455–486, 2016, doi:10.1007/s11225-015-9647-7; read as arXiv:1509.02060v1, <https://arxiv.org/abs/1509.02060v1>: Theorem 2, Corollaries 1 and 2, Theorem 6 and Section 4 of arXiv:1509.02060v1.
