# Trace inclusion of ping-pong protocols is undecidable

For deterministic ping-pong protocols with an unbounded number of sessions, standard randomized encryption and signatures, no pairing and one message variable per rule, trace inclusion is undecidable, and trace equivalence becomes undecidable once a nondeterministic choice is allowed.

**Theorem (Chrétien, Cortier and Delaune).** For protocols of the class $C_{pp}$ of [ping-pong protocols with one message variable per rule](ping-pong-protocols-with-one-variable.md):

1. it is undecidable, given two protocols $P$ and $Q$ in $C_{pp}$, whether $P \sqsubseteq Q$ (Theorem 3.6);
2. it is undecidable, given three protocols $P$, $Q_1$, $Q_2$ in $C_{pp}$, whether $P$ is trace equivalent to $Q_1 + Q_2$, where $+$ is nondeterministic choice, which silently becomes $Q_1$ or $Q_2$ (Corollary 3.7).

The protocols are the input; replication allows unboundedly many sessions. By contrast, trace equivalence of two protocols of $C_{pp}$ is decidable (Theorem 3.5), and the secrecy problem is decidable for this class.

## Depends on

- [Ping-pong protocols with one message variable per rule](ping-pong-protocols-with-one-variable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Clause 1 encodes the Post correspondence problem directly into trace inclusion between two protocols of $C_{pp}$ (Appendix A); alternatively it follows from the source's reverse translation of real-time generalized deterministic pushdown automata into protocols and the undecidability of language inclusion for deterministic pushdown automata. For clause 2, take $P$ and $Q_1$ from clause 1 and $Q_2 = P$: then $P \sqsubseteq Q_1 + Q_2$ always holds, so $P$ and $Q_1 + Q_2$ are trace equivalent iff $Q_1 \sqsubseteq P$.

## Sources

- Rémy Chrétien, Véronique Cortier and Stéphanie Delaune, "From security protocols to pushdown automata", *ACM Transactions on Computational Logic* 17(1), Article 3, 45 pages, 2015, doi:10.1145/2811262; read in the authors' open-access copy at <https://members.loria.fr/VCortier/files/Papers/CCD-Tocl15.pdf>: Theorems 3.5 and 3.6, Corollary 3.7 and Appendix A of that copy.
- Stéphanie Delaune and Lucca Hirschi, "A survey of symbolic methods for establishing equivalence-based properties in cryptographic protocols", *Journal of Logical and Algebraic Methods in Programming* 87:127–144, 2017, doi:10.1016/j.jlamp.2016.10.005; read as arXiv:1610.08279v1, <https://arxiv.org/abs/1610.08279v1>: Section 5.2.1 of arXiv:1610.08279v1, which presents the undecidability of equivalence for this fragment.
