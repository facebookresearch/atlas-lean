# The calculus of relations with one character is undecidable

Validity of equations between relation terms built from a single relation letter using only composition, union and complement is undecidable, and so is validity over finite structures.

**Theorem (Nakamura).** Let $a$ be a single character. Both the validity problem and the finite validity problem for $\mathrm{Eq}[T^{\langle \cdot, {}^-, \cup\rangle}_{\{a\}}]$ are undecidable: there is no algorithm that decides, given terms $t, u$ of the [calculus of relations](calculus-of-relations.md) built from $a$ by composition $\cdot$, complement ${}^-$ and union $\cup$ only (no converse, no identity constant), whether $[\![t]\!]_M = [\![u]\!]_M$ holds in every model $M$, nor whether it holds in every finite model.

The same holds with the identity constant added (Theorem 12 of the source, signature $\langle \cdot, {}^-, \cup, 1\rangle$) and for two characters over $\langle \cdot, {}^-, \cup\rangle$ (Corollary 14). By contrast, equations over $\langle \cdot, \cup\rangle$ (even with converse, identity, $0$, $\top$, intersection and atomic negation) and over $\langle {}^-, \cup\rangle$ (even with converse and identity) have decidable validity and finite validity (Theorem 19 of the source, part (1) after Andréka and Bredikhin).

## Depends on

- [Calculus of relations](calculus-of-relations.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)

## Expansion

The proof is a chain of reductions, each preserving both validity and finite validity. First-order validity reduces to validity of three-variable formulas over countably many binary relation symbols without equality (the $\forall\exists\forall$ conservative reduction class of Kahr, Moore and Wang, as presented by Börger, Grädel and Gurevich, Theorem 3.1.9), hence by Tarski's translation to equations over countably many characters with the full signature (Lemma 5). Converse and identity are then eliminated with fresh characters constrained by equations (Lemmas 7 and 9, Corollary 10), countably many characters are encoded by two (Lemma 11), and two characters $a_1, a_2$ are finally encoded by one character $a$, using the relations $a \cap a^2$ and $a \cap a^3$ to mark the parts of a model that carry the original relations (Lemma 16 with the axioms (Ax.1), (Ax.2) and Proposition 15).

The conference version stated (Ax.1) and (Ax.2) in a form for which Proposition 15 fails; the long version corrects the two axioms and leaves the rest of the proof unchanged (remark at the end of its Section 3).

## Sources

- Y. Nakamura, "The Undecidability of FO3 and the Calculus of Relations with Just One Binary Relation", in *Logic and Its Applications (ICLA 2019)*, Lecture Notes in Computer Science 11600, Springer, 2019, pp. 108–120, <https://doi.org/10.1007/978-3-662-58771-3_11>; numbers from the corrected long version arXiv:2610.35770v1, <https://arxiv.org/abs/2610.35770v1>: Theorem 17, with Lemmas 5, 7, 9, 11 and 16, Theorem 12, Corollary 14, Theorem 19, and the correction remark at the end of Section 3.
- E. Börger, E. Grädel and Y. Gurevich, *The Classical Decision Problem*, Perspectives in Mathematical Logic, Springer, 1997, <https://doi.org/10.1007/978-3-642-59207-2>: Theorem 3.1.9 (the $\forall\exists\forall$ class is a conservative reduction class); not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Lemma 1).
