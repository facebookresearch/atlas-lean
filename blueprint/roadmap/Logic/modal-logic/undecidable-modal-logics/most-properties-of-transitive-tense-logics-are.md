# Most properties of transitive tense logics are undecidable

Over the minimal transitive tense logic $\mathsf{K4}_t$, it is undecidable whether the extension by a given formula is consistent, Kripke complete, canonical, first-order definable, has the finite model property, is locally tabular, tabular or decidable; the same holds over the minimal tense logic $\mathsf{K}_t$.

**The frame $\mathfrak{G}$.** Fix a Minsky (two-counter) machine $M$ and a configuration $\langle s, n, m\rangle$ from which reachability is undecidable (Theorem 2.4 of the source), and let $\mathrm{Reach}$ be the set of configurations $\langle t, k, l\rangle$ reachable from it. $\mathfrak{G} = (W, R, \mathcal{A})$ is the general frame with $W = \mathrm{Reach} \cup \{a_i, b_i, c_i : i < \omega\} \cup \{a', b', b''\}$, with $R$ the transitive closure of the pairs $(c_i, c_j)$, $(a_i, a_j)$, $(b_i, b_j)$ for $j < i$, the pairs $(a', a_0)$, $(b', b_0)$, $(b', b'')$, and, for each $\langle t, k, l\rangle \in \mathrm{Reach}$, the pairs from $\langle t, k, l\rangle$ to itself, to $c_t$, to $a_k$ and to $b_l$; and with $\mathcal{A}$ the subsets of $W$ whose intersection with $\{c_i : i < \omega\}$ is finite or cofinite (Definition 3.1).

**Theorem (Chen and Takahashi).** Let $P$ be a property of logics in [$\mathrm{NExt}\,\mathsf{K4}_t$](normal-extensions-of-transitive-tense-logic.md) and $\alpha \in \mathcal{L}_t$ a formula such that $\mathsf{K4}_t \oplus \alpha$ has $P$, $\mathfrak{G} \not\models \alpha$, and every logic with $P$ is Kripke complete or decidable. Then the set $\{\varphi \in \mathcal{L}_t : \mathsf{K4}_t \oplus \varphi \text{ has } P\}$ is undecidable (Theorem 3.5 of the source).

**Corollary.** Each of the following sets is undecidable: the $\varphi$ such that $\mathsf{K4}_t \oplus \varphi$ is Kripke complete; canonical; first-order definable; has the finite model property; is locally tabular; is tabular; is decidable; equals a fixed tabular logic $L$; is consistent. The same properties are undecidable in $\mathrm{NExt}\,\mathsf{K}_t$.

In the corollary, $\alpha = \Box\bot \wedge \blacksquare\bot$ works for the first seven properties: $\mathsf{K4}_t \oplus \alpha$ is the logic of the one-point irreflexive frame, which is tabular and so has all of them, and $\mathfrak{G}$ refutes it. In contrast, consistency is decidable in $\mathrm{NExt}\,\mathsf{K}$, and consistency, Kripke completeness, the finite model property and decidability are decidable in the lattice of extensions of the tense logic of linear frames.

## Depends on

- [Normal extensions of transitive tense logic](normal-extensions-of-transitive-tense-logic.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof adapts the method of Chagrov and Shehtman. There is a deterministic two-register Minsky machine $M$ and a configuration $c_0$ from which reachability is undecidable. A transitive general frame $\mathfrak{G}$, whose points code the reachable configurations together with chains $a_n$, $b_n$, $c_n$ for register values and states, has points named by variable-free formulas. Each configuration $c$ is mapped computably to a finitely axiomatized logic $L(c) \in \mathrm{NExt}\,\mathsf{K4}_t$ such that $L(c) = \mathsf{K4}_t \oplus \alpha$ when $c$ is reachable from $c_0$, while otherwise $\mathfrak{G}$ validates $L(c)$ and $L(c)$ is Kripke incomplete and undecidable, so lacks $P$. Deciding $P$ would therefore decide reachability. The result for $\mathsf{K}_t$ follows because $\mathsf{K4}_t = \mathsf{K}_t \oplus (\Diamond\Diamond p \to \Diamond p)$ is a finite extension.

## Sources

- Q. Chen and T. Takahashi, "Most properties are undecidable for transitive tense logics", Electronic Proceedings in Theoretical Computer Science 447, 2026, pp. 189–202, doi:10.4204/EPTCS.447.11; read as arXiv:2606.31863v1, <https://arxiv.org/abs/2606.31863v1>: the main theorem of Section 3 (label thm:reduction-K4t-P), the corollary listing the undecidable properties (label Thm:undec-properties) with its proof, and the remark extending them to $\mathrm{NExt}\,\mathsf{K}_t$.
