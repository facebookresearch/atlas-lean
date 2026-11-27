# Relational Robinson arithmetic is essentially undecidable over a weak substructural logic

A version of Robinson's arithmetic R with addition and multiplication given as ternary relations is essentially undecidable already over a propositional logic much weaker than intuitionistic logic, extended by minimal first-order axioms.

**Theorem (Badia, Cintula, Hájek and Tedder).** Let $\mathrm L_0$ be the propositional logic in the language $\to, \wedge, \vee, \bot$ (with $\neg\varphi = \varphi \to \bot$ and $\varphi \leftrightarrow \psi = (\varphi \to \psi) \wedge (\psi \to \varphi)$) axiomatized by lattice logic together with the rules of weakening $\varphi \rhd \psi \to \varphi$, modus ponens, assertion $\varphi \rhd (\varphi \to \psi) \to \psi$ and the further rules of the source's Hilbert system, and let $\mathrm{QL}_0$ be its first-order extension of Section 4 of the source, over the language with $0$, successor $S$, binary predicates $=$ and $\le$ and ternary predicates $A$ and $M$. Let $\mathrm R^\sim$ be the theory with the axioms, for all numerals $m, n$ and variables $x$,

$$
A(m, n, x) \leftrightarrow x = m + n, \quad M(m, n, x) \leftrightarrow x = m \cdot n, \quad m \neq n \ \text{for distinct numerals}, \quad x \le n \leftrightarrow \bigvee_{k \le n} x = k, \quad x \le n \vee n \le x, \quad x \le n \vee \neg(x \le n).
$$

A theory is *essentially undecidable* in a logic if it is consistent and every consistent theory extending it in that logic is undecidable. Then $\mathrm R^\sim$ is essentially undecidable in $\mathrm{QL}_0$ (Theorem 4.10 of the source). Consequently, for every propositional logic expanding $\mathrm L_0$ and predicate logic expanding $\mathrm{QL}_0$, every theory extending $\mathrm R^\sim$ that does not prove both a $\Sigma_1$-formula and its negation is essentially undecidable (Corollary 4.11).

[Robinson's $\mathsf Q$](../../../first-order-logic/peano-arithmetic-and-robinson-s-q/qtheory.md) is essentially undecidable in intuitionistic logic, and Hájek proved essential undecidability of Grzegorczyk's relational variant $\mathsf Q^\sim$ in the fuzzy logic BL; the theorem weakens both the logic and the theory. In a stronger logic $\mathrm{QSL}_w$, $\mathsf Q^\sim$ is essentially undecidable (Corollary 6.16).

## Depends on

None.

## Proof depends on

None.

## Expansion

The proof follows Kleene's structural form of Rosser's argument. A theory is *Rosser* in a logic if every pair of disjoint recursively enumerable sets is separated by a $\Sigma_1$-formula provable for members of one set and refutable for members of the other; a consistent Rosser theory is essentially undecidable (Theorem 2.5), because there are disjoint recursively enumerable sets that no recursive set separates. For $\mathrm R^\sim$ one shows soundness in the standard model, $\Sigma_1$-completeness for numerical instances (Theorem 4.8) and the separation property (Lemma 4.9), using only the rules of $\mathrm{QL}_0$.

## Sources

- G. Badia, P. Cintula, P. Hájek and A. Tedder, "How Much Propositional Logic Suffices for Rosser's Essential Undecidability Theorem?", *The Review of Symbolic Logic* 15(2):487–504, 2022 (published online 2020), <https://doi.org/10.1017/S175502032000012X>; numbers from arXiv:2006.12275v1, <https://arxiv.org/abs/2006.12275v1>: Section 1 (the axioms of $\mathrm R^\sim$ and $\mathsf Q^\sim$), Section 2 (Definitions 2.2 and 2.4, Theorem 2.5), Section 3 (the logic $\mathrm L_0$), Section 4 (the logic $\mathrm{QL}_0$, Theorems 4.8 and 4.10, Lemma 4.9, Corollary 4.11) and Corollary 6.16.
