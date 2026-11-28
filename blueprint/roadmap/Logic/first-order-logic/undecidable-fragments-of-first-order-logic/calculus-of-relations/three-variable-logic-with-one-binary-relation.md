# Three-variable logic with one binary relation is undecidable

Validity of first-order formulas with at most three variables over a signature consisting of a single binary relation symbol, without equality, is undecidable; so is validity over finite structures.

**Theorem (Nakamura).** Let $a$ be a binary relation symbol, and let $\mathrm{FO}^3_{\{a\}}$ be the set of first-order formulas built from atoms $a(x, y)$ (with variables $x, y$, possibly equal) by $\vee$, $\neg$ and $\exists$, containing at most three distinct variables, free or bound, with no equality symbol, no constants and no function symbols; variables may be requantified. A formula is *valid* (*finitely valid*) if it holds under every assignment in every structure (every finite structure) $(|M|, R)$ with $|M| \neq \emptyset$ and $R \subseteq |M|^2$. The validity problem and the finite validity problem for $\mathrm{FO}^3_{\{a\}}$ are both undecidable.

This is the least undecidable case along both of its restrictions: monadic first-order logic (Löwenheim) and two-variable first-order logic, even with equality (Mortimer; Grädel, Kolaitis and Vardi), are decidable.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The calculus of relations with one character is undecidable](calculus-of-relations-with-one-character.md)
- [Calculus of relations](calculus-of-relations.md)

## Expansion

Each term $t$ over $\langle \cdot, {}^-, \cup\rangle$ in the single character $a$ translates into a formula $G(t, i, j)$ of three-variable logic with free variables $x_i, x_j$ defining the relation $[\![t]\!]_M$ in every model (Lemma 3 of the source, after Tarski); when $t$ does not contain the identity constant $1$, the formula contains no equality. An equation $t = u$ is then valid (finitely valid) exactly when $\forall x_1 \forall x_2\,(G(t, 1, 2) \leftrightarrow G(u, 1, 2))$ is, so the undecidability of the one-character calculus of relations transfers.

## Sources

- Y. Nakamura, "The Undecidability of FO3 and the Calculus of Relations with Just One Binary Relation", in *Logic and Its Applications (ICLA 2019)*, Lecture Notes in Computer Science 11600, Springer, 2019, pp. 108–120, <https://doi.org/10.1007/978-3-662-58771-3_11>; numbers from the corrected long version arXiv:2610.35770v1, <https://arxiv.org/abs/2610.35770v1>: Section 2 (the logics $\mathrm{FO}^k_A$ and validity), Lemma 3, Theorem 18 and Section 1 (the decidable monadic and two-variable cases).
