# Validity in separation logic with points-to, zero and successor is Π⁰₁-complete

First-order logic over a finite heap on the natural numbers, with only equality, the points-to atom, zero and successor, and no separating conjunction or magic wand, has a $\Pi^0_1$-complete validity problem under its standard interpretation.

**The fragment $\mathrm{SL}_{\mathbb{N}}$ (Ito and Tatsuta).** Terms are $t ::= x \mid 0 \mid s(t)$ and formulas are

$$
A ::= t = t \mid t \hookrightarrow t \mid \neg A \mid A \wedge A \mid A \vee A \mid \exists x\, A \mid \forall x\, A.
$$

In the standard interpretation addresses and values are natural numbers, $0$ and $s$ denote zero and successor, a heap is a finite partial function $h : \mathbb{N} \rightharpoonup \mathbb{N}$, quantifiers range over $\mathbb{N}$, and $\sigma, h \models t_1 \hookrightarrow t_2$ holds iff $h(\sigma(t_1)) = \sigma(t_2)$. A formula is *valid* if $\sigma, h \models A$ for every variable assignment $\sigma$ and every heap $h$.

**Theorem (Ito and Tatsuta).** The set of valid $\mathrm{SL}_{\mathbb{N}}$ formulas is $\Pi^0_1$-complete; in particular validity of $\mathrm{SL}_{\mathbb{N}}$ formulas is undecidable.

Validity here is with respect to the standard interpretation over $\mathbb{N}$, not the usual separation logic validity that ranges over arbitrary sets of addresses. The fragment contains neither separating conjunction nor magic wand.

## Depends on

- [The arithmetical class Πₙ](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

None.

## Expansion

Hardness: a translation $A \mapsto A^{\square\circ}$ maps each $\Pi^0_1$ sentence of Peano arithmetic to an $\mathrm{SL}_{\mathbb{N}}$ formula that is valid exactly when $A$ is true in the standard model; addition and multiplication are not available, so the translated formula refers to an operation table for addition, multiplication and inequality kept in the heap, guarded by a table heap condition. Truth of $\Pi^0_1$ sentences of arithmetic is $\Pi^0_1$-complete. The paper also gives a second undecidability proof from Trakhtenbrot's theorem on validity in all finite structures. Membership: model checking, deciding $\sigma, h \models A$ for a given assignment and finite heap, is decidable (Proposition 7.8), so validity, a universal statement over all assignments and heaps, is in $\Pi^0_1$.

## Sources

- Sohei Ito and Makoto Tatsuta, "Encoding Peano Arithmetic in a Minimal Fragment of Separation Logic", Logical Methods in Computer Science 22(2), Article 22, 2026, <https://doi.org/10.46298/lmcs-22(2:22)2026>; Theorem 7.10 (main statement), Propositions 7.1, 7.8 and 7.9, Theorem 5.4 and Corollary 5.5, and the definition of $\mathrm{SL}_{\mathbb{N}}$ in Section 3 of arXiv:2507.00465v4 (the copy read), <https://arxiv.org/abs/2507.00465v4>.
