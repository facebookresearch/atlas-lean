# Calculus of relations

The calculus of relations is the equational language of binary relations: terms are built from relation letters by composition, complement, union, converse and the identity, and an equation $t = u$ is valid when both sides denote the same relation in every structure.

**Definition.** Let $A$ be a set of *characters* (binary relation letters). The *terms* over $A$ are given by

$$
t, u ::= a \mid t \cdot u \mid t^- \mid t \cup u \mid t^\smile \mid 1 \qquad (a \in A).
$$

For a subsequence $\varsigma$ of the signature $\langle \cdot, {}^-, \cup, {}^\smile, 1\rangle$, $T^\varsigma_A$ is the set of terms over $A$ using only the operations in $\varsigma$. A *model* $M$ over $A$ is a nonempty set $|M|$ with a binary relation $R^M(a) \subseteq |M|^2$ for each $a \in A$. The value $[\![t]\!]_M \subseteq |M|^2$ is defined by $[\![a]\!]_M = R^M(a)$, relational composition $[\![t \cdot u]\!]_M = \{(v, v') \mid \exists v''\ (v, v'') \in [\![t]\!]_M,\ (v'', v') \in [\![u]\!]_M\}$, complement relative to $|M|^2$, union, converse $[\![t^\smile]\!]_M = \{(v', v) \mid (v, v') \in [\![t]\!]_M\}$, and $[\![1]\!]_M = \{(v, v) \mid v \in |M|\}$. An *equational formula* is an expression $t = u$ with $t, u$ terms; $M \models t = u$ iff $[\![t]\!]_M = [\![u]\!]_M$. The formula is *valid* (*finitely valid*) if it holds in every model (every finite model) over $A$; $\mathrm{Eq}[T^\varsigma_A]$ denotes the equational formulas between terms of $T^\varsigma_A$, and its *validity problem* (*finite validity problem*) asks whether a given such formula is valid (finitely valid). Abbreviations: $t \cap u = (t^- \cup u^-)^-$, $\top = a \cup a^-$, $0 = a \cap a^-$.

Boolean combinations of equations reduce to single equations of the form $t = 0$ without using converse or the identity (Lemma 2 of the source, following Maddux). With equality, three-variable first-order logic over binary relations and terms of the calculus of relations define the same binary relations (Tarski and Givant).

## Depends on

None.

## Proof depends on

None.

## Expansion

The translation of a term into a three-variable first-order formula defining the same relation proceeds by recursion on the term, reusing the bound variable for composition: $t \cdot u$ becomes $\exists x_3\,(\varphi_t(x_1, x_3) \wedge \varphi_u(x_3, x_2))$ with the variables renamed so that three suffice. The converse translation from three-variable formulas to terms is Tarski's (Lemma 4 of the source).

## Sources

- Y. Nakamura, "The Undecidability of FO3 and the Calculus of Relations with Just One Binary Relation", in *Logic and Its Applications (ICLA 2019)*, Lecture Notes in Computer Science 11600, Springer, 2019, pp. 108–120, <https://doi.org/10.1007/978-3-662-58771-3_11>; numbers from the corrected long version arXiv:2610.35770v1, <https://arxiv.org/abs/2610.35770v1>: Section 2 (terms, semantics, equational formulas, Lemmas 2 to 4).
- A. Tarski and S. Givant, *A Formalization of Set Theory without Variables*, American Mathematical Society Colloquium Publications 41, 1987, <https://doi.org/10.1090/coll/041>: the equivalence of three-variable logic and the calculus of relations (p. 28 and Section 3.9); not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Lemmas 3 and 4).
