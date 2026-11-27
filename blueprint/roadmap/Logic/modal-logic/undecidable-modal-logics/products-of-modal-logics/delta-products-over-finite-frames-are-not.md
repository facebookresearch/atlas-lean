# δ-products over finite frames are not recursively enumerable

When one component class of a δ-product contains only finite frames, while the horizontal class contains successor chains with a spy point and the vertical class contains fans of every size, the logic of the resulting δ-product frames is not recursively enumerable.

**Theorem (Hampson, Kikot and Kurucz).** Let $\mathcal{C}_h$ and $\mathcal{C}_v$ be classes of unimodal frames such that

1. $\mathcal{C}_h$ or $\mathcal{C}_v$ contains only finite frames;
2. $\mathfrak{H}_\omega \in \mathcal{C}_h$, or $\mathfrak{H}_k \in \mathcal{C}_h$ for every $k < \omega$;
3. $\mathcal{C}_v$ contains an $\omega$-fan, or $\mathcal{C}_v$ contains a $k$-fan for every $k < \omega$.

Then $\mathrm{Log}(\mathcal{C}_h \times^\delta \mathcal{C}_v)$ is not recursively enumerable (Theorem 3).

The frames $\mathfrak{H}_k$ (successor chain on $k$ with a spy point) and $k$-fans are defined on the [δ-products](delta-products-of-modal-logics.md) page.

## Depends on

- [Delta-products of modal logics](delta-products-of-modal-logics.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [δ-products with a K component are undecidable](delta-products-with-a-k-component-are.md)

## Expansion

The proof modifies the grid-and-faulty-runs encoding of the $\mathbf{K}$-component theorem into a reduction of counter machine reachability (whether a run reaches a given state; $\Sigma^0_1$-hard) to satisfiability in $\mathcal{C}_h \times^\delta \mathcal{C}_v$: a fresh variable marks where the vertical grid generation may stop, so the grid can be finite. Hence satisfiability is $\Sigma^0_1$-hard, so validity, which is non-satisfiability of the negation, is $\Pi^0_1$-hard and the logic is not recursively enumerable.

## Sources

- Christopher Hampson, Stanislav Kikot and Agi Kurucz, "The decision problem of modal product logics with a diagonal, and faulty counter machines", *Studia Logica* 104(3):455–486, 2016, doi:10.1007/s11225-015-9647-7; read as arXiv:1509.02060v1, <https://arxiv.org/abs/1509.02060v1>: Theorem 3 and its proof sketch in Section 4 of arXiv:1509.02060v1.
