# Synthesis for fragments of interval temporal logic is undecidable

The synthesis problem for the interval logic with meets, met by, begun by and begins is undecidable over finite linear orders, and already its fragment without met by is undecidable over the natural numbers, although satisfiability of that fragment over the naturals is decidable.

**Theorem (Montanari and Sala).** For the [synthesis problem for interval temporal logic](synthesis-problem-for-interval-temporal-logic.md):

1. the finite synthesis problem for $\mathsf{A\bar{A}B\bar{B}}$ is undecidable (Corollary 1);
2. the $\mathbb{N}$-synthesis problem for $\mathsf{AB\bar{B}}$ is undecidable (Theorem 5).

The input is a formula together with the set of letters and temporal requests controlled by the spoiler. Consequently synthesis is undecidable for $\mathsf{A\bar{A}B\bar{B}}{\sim}$ over both kinds of domains and for $\mathsf{A\bar{A}B\bar{B}}$ and $\mathsf{AB\bar{B}}{\sim}$ over $\mathbb{N}$. By contrast, satisfiability of $\mathsf{AB\bar{B}}$ over $\mathbb{N}$ and of $\mathsf{A\bar{A}B\bar{B}}$ over finite orders is decidable, finite synthesis for $\mathsf{AB\bar{B}}{\sim}$ is decidable, and finite synthesis for $\mathsf{AB\bar{B}}$ is non-primitive-recursive-hard (Theorem 4).

## Depends on

- [Synthesis problem for interval temporal logic with an equivalence over points](synthesis-problem-for-interval-temporal-logic.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Clause 1 reduces the $0$-$0$ reachability problem for Minsky counter machines (undecidable, Theorem 1) to finite synthesis: a formula $\varphi^{0\text{-}0}_{\mathcal{M}}$ encodes computations of $\mathcal{M}$, and the power of synthesis is used to force that the encoding of consecutive counter values is injective, while $\langle\bar{A}\rangle$ is needed only to force surjectivity; then $\mathcal{M}$ reaches $0$-$0$ iff the formula is a positive instance (Theorem 3). Dropping surjectivity leaves only lossy simulations in $\mathsf{AB\bar{B}}$, which yields non-primitive-recursive hardness. Clause 2 is derived in the same way from the undecidability of satisfiability for $\mathsf{AB\bar{B}}{\sim}$ over $\mathbb{N}$, an earlier result of the same authors, with synthesis taking over the role of the equivalence relation.

## Sources

- Angelo Montanari and Pietro Sala, "Interval-based synthesis", in *Proceedings Fifth International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2014)*, Electronic Proceedings in Theoretical Computer Science 161, 2014, pp. 102–115, doi:10.4204/EPTCS.161.11; read as arXiv:1408.5960v1, <https://arxiv.org/abs/1408.5960v1>: Corollary 1, Theorems 1, 3, 4 and 5, Table 1 and Section 4 of arXiv:1408.5960v1.
