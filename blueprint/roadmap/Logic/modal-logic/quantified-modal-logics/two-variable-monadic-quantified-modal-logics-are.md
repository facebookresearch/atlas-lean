# Two-variable quantified modal logics with one monadic letter are undecidable

Every logic between $\mathbf{QK}$ and $\mathbf{QGL}$, between $\mathbf{QK}$ and $\mathbf{QGrz}$, or between $\mathbf{QK}$ and $\mathbf{QKTB}$ is undecidable already for formulas with two individual variables and a single monadic predicate letter, without constants, function symbols or equality.

**Theorem (Rybakov and Shkatov).** Let $L$ be a [quantified modal logic](quantified-modal-logic-ql.md) such that

$$
\mathbf{QK} \subseteq L \subseteq \mathbf{QGL}, \quad \text{or} \quad \mathbf{QK} \subseteq L \subseteq \mathbf{QGrz}, \quad \text{or} \quad \mathbf{QK} \subseteq L \subseteq \mathbf{QKTB}.
$$

Then $L$ is undecidable in the language with two individual variables and a single monadic predicate letter: no algorithm decides, for formulas built from one unary predicate letter $P$ and the two variables $x, y$ with $\wedge$, $\neg$, $\Box$ and $\forall$, whether they belong to $L$. In particular $\mathbf{QK}$, $\mathbf{QT}$, $\mathbf{QD}$, $\mathbf{QK4}$, $\mathbf{QS4}$, $\mathbf{QGL}$, $\mathbf{QGrz}$, $\mathbf{QKB}$ and $\mathbf{QKTB}$ are undecidable in this language.

The first two intervals are Theorem 2.6 and the third is Theorem 2.11 of the source. Remark 2.8 there states that the result for the first two intervals also holds when each logic is extended by the Barcan formula $\forall x\, \Box P(x) \to \Box\, \forall x\, P(x)$, which restricts to frames with constant domains. The bound is tight in one direction: for $\mathbf{QK}$, $\mathbf{QT}$, $\mathbf{QK4}$ and $\mathbf{QS4}$, additionally requiring that $\Box$ apply only to formulas with at most one free variable gives decidable fragments (Wolter and Zakharyaschev, 2001).

## Depends on

- [Quantified modal logic $\mathbf{Q}L$](quantified-modal-logic-ql.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Kontchakov, Kurucz and Zakharyaschev (2005) reduce the tiling problem for $\mathbb{N} \times \mathbb{N}$ to satisfiability of two-variable formulas with infinitely many monadic letters in every logic whose frames contain a world seeing infinitely many worlds, each of which sees infinitely many further worlds; $\mathbf{QK}$, $\mathbf{QGL}^{sem}$ and $\mathbf{QGrz}^{sem}$ qualify. The source first refines this to a sublemma: satisfiability of suitable two-variable monadic formulas is undecidable for $L \in \{\mathbf{QK}, \mathbf{QGL}^{sem}, \mathbf{QGrz}^{sem}\}$. It then adapts Halpern's technique for single-variable propositional fragments: each monadic letter $P_i$ is replaced by a formula built from the single letter $P$ and modal prefixes that, in a suitably shaped model, picks out the worlds encoding $P_i$, without introducing new individual variables. Since the encoded formula is satisfiable in the weakest logic iff in the strongest one, every logic in the interval is undecidable. For $\mathbf{QKTB}$ the same argument runs on reflexive symmetric frames.

## Sources

- M. Rybakov and D. Shkatov, "Undecidability of first-order modal and intuitionistic logics with two variables and one monadic predicate letter", *Studia Logica* 107(4):695–717, 2019, doi:10.1007/s11225-018-9815-7; read as arXiv:1706.05060v5, <https://arxiv.org/abs/1706.05060v5>: Theorem 2.6, Corollary 2.7, Theorem 2.11 and Corollary 2.12 of arXiv:1706.05060v5, and Remark 2.8.
