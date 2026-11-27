# Interpolant existence for two-variable logic with two equivalence relations is undecidable

For two-variable first-order logic with two binary predicates interpreted as equivalence relations, a decidable logic, it is undecidable whether two given formulas have a Craig interpolant in that logic.

**Theorem (Wolter and Zakharyaschev).** Let $\sigma$ be a signature of unary and binary predicates including two distinguished binary predicates $E_1, E_2$, and let $\mathrm{FO}^2\mathrm{2E}(\sigma)$ be the set of constant-free first-order formulas over $\sigma$ in two variables $x, y$, with equality, interpreted in structures where $E_1$ and $E_2$ denote equivalence relations. For formulas $\varphi(\bar x), \psi(\bar x)$ with the same free variables and shared signature $\varrho = \mathrm{sig}(\varphi) \cap \mathrm{sig}(\psi)$, an *$\mathrm{FO}^2\mathrm{2E}$-interpolant* is an $\mathrm{FO}^2\mathrm{2E}(\varrho)$-formula $\iota(\bar x)$ with $\varphi \models \iota$ and $\iota \models \psi$. The *interpolant existence problem* (IEP), given $\varphi$ and $\psi$, asks whether such an interpolant exists. The $\mathrm{FO}^2\mathrm{2E}$-IEP is undecidable, and so is the explicit definition existence problem (EDEP): given $\varphi$, $\psi$ and a signature $\varrho$, is there an explicit $\varrho$-definition of $\psi$ modulo $\varphi$ in the logic?

The same holds for the two-variable guarded fragment with individual constants and two equivalence relations, $\mathrm{GF}^2\mathrm{2E}_c$ (Theorem 6), and for the description logic $\mathcal{ALC}^{\cap, \neg, \mathrm{id}}\mathrm{2E}$, ALC with role intersection, role negation, the identity role and two equivalence relations, for concept inclusions (Theorem 7). Validity in $\mathrm{FO}^2\mathrm{2E}$ and $\mathrm{GF}^2\mathrm{2E}_c$ is decidable (co-2NEXPTIME-complete and 2EXPTIME-complete), but these logics lack the Craig interpolation property, which full first-order logic has ([Craig interpolation for first-order logic](../../../proof-theory/craig-interpolation-for-first-order-logic.md)), so the IEP does not reduce to validity. These are the first decidable fragments of first-order logic shown to have an undecidable IEP.

## Depends on

- [Equivalence relation](../../../../Order/ordered-sets/equivalence-relation.md)

## Proof depends on

None.

## Expansion

An interpolant exists iff there are no pointed structures $\mathfrak A, \bar a \models \varphi$ and $\mathfrak B, \bar b \models \neg\psi$ that are $\mathrm{FO}^2\mathrm{2E}(\varrho)$-bisimilar, for a notion of global two-variable bisimulation respecting partial $\varrho$-isomorphisms (Lemma 2). The proof reduces the infinite Post correspondence problem ($\omega$PCP: is there an infinite sequence of indices making the two $\omega$-words coincide?), undecidable by Ruohonen and by Gire. With shared signature $\{R, S\} \cup \Gamma$, where $R$ and $S$ are binary and the letters of $\Gamma$ are unary predicates, formulas $\varphi(x)$ and $\psi(x)$ are built such that the instance has a solution iff $\varphi(x)$ and $\neg\psi(x)$ are satisfied in bisimilar pointed structures; $\varphi$ generates $S$-chains and an $R$-cycle with three points, its only unguarded conjunct being $\forall x, y\,((X_0(x) \wedge X_0(y)) \to x = y)$ (Theorem 4). The EDEP is polynomially interreducible with the IEP (Lemma 3).

## Sources

- F. Wolter and M. Zakharyaschev, "Interpolant Existence is Undecidable for Two-Variable First-Order Logic with Two Equivalence Relations", in *Proceedings of the 37th International Workshop on Description Logics (DL 2024)*, CEUR Workshop Proceedings 3739, 2024, paper 11, <https://ceur-ws.org/Vol-3739/paper-11.pdf>; numbers from arXiv:2404.02683v1, <https://arxiv.org/abs/2404.02683v1>: Section 2 (the fragments, Definitions 1 to 3, Lemmas 2 and 3), Section 3 (Theorems 4 and 5), Section 4 (Theorems 6 and 7).
- F. Gire, "Two decidability problems for infinite words", *Information Processing Letters* 22(3):135–140, 1986, <https://doi.org/10.1016/0020-0190(86)90058-X>: undecidability of the infinite Post correspondence problem, as recalled in Section 3 of the version of the first source read.
