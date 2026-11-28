# Intuitionistic provability of Δ₂ formulas in the Mints hierarchy is undecidable

Provability in intuitionistic first-order logic is undecidable already for formulas built from implication and universal quantification at the level $\Delta_2$ of the Mints hierarchy, and even when all predicates are unary.

**Theorem (Schubert, Urzyczyn and Zdanowski).** Consider intuitionistic first-order logic without function symbols and equality, restricted to the $(\forall,\to)$-fragment, and the class $\Delta_2 = \Sigma_2 \cap \Pi_2$ of the [Mints hierarchy](mints-hierarchy-of-implicational-universal.md).

1. It is undecidable whether a given $\Delta_2$ formula is provable (Theorem 4.5).
2. This remains undecidable for $\Delta_2$ formulas in which all predicate symbols are unary (Theorem 4.9).

The signature is part of the input in clause 1, and in clause 2 consists of unary predicates only. Provability for every class containing $\Delta_2$ (such as $\Sigma_2$, $\Pi_2$ and all higher levels) is therefore undecidable too, while for $\Sigma_1$ it is EXPSPACE-complete.

## Depends on

- [Mints hierarchy of implicational-universal formulas](mints-hierarchy-of-implicational-universal.md)
- [Quantified intuitionistic logic QInt](quantified-intuitionistic-logic-qint.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the solvability of deterministic tiling puzzles to provability (Section 3.1): a puzzle $\langle T, R, E, ok\rangle$ with a finite set $T$ of tiles and $R : T^4 \to T$ determines a unique tiling $G^\ast$ of $\mathbb N \times \mathbb N$, with $E$ on both axes and $G^\ast(m+1, n+1) = R(G^\ast(m, n+1), G^\ast(m, n), G^\ast(m+1, n), G^\ast(m+2, n))$, and it is solvable when $ok$ occurs in $G^\ast$. Solvability is undecidable (Lemma 3.1, by reduction from whether a deterministic Turing machine accepts the empty input); a good expansion links a page for that lemma. In the reduction, each puzzle is effectively translated into a $\Delta_2$ formula that is provable iff the puzzle is solvable (the two directions are separate lemmas of Section 4). Since the formulas used are "easy" in the source's sense, a translation (Section 4.1) $\varphi \mapsto \overline{\varphi}$ that replaces predicates of higher arity by unary predicates with auxiliary symbols preserves provability and gives clause 2. Earlier, undecidability of $\Pi_2$ for the full language with one binary predicate followed from a result of Orevkov, and the conference version of the paper had shown undecidability of $\Pi_2$ in the $(\forall,\to)$-fragment.

## Sources

- Aleksy Schubert, Paweł Urzyczyn and Konrad Zdanowski, "On the Mints hierarchy in first-order intuitionistic logic", *Logical Methods in Computer Science* 12(4):11, 2016, doi:10.2168/LMCS-12(4:11)2016; read as arXiv:1610.02675v3, <https://arxiv.org/abs/1610.02675v3>: Theorems 4.5 and 4.9, Lemma 3.1 and Sections 3 and 4 of arXiv:1610.02675v3.
