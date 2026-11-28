# Relational Robinson arithmetic is essentially undecidable over a weak substructural logic

A version of Robinson's arithmetic R with addition and multiplication given as ternary relations is essentially undecidable already over a propositional logic much weaker than intuitionistic logic, extended by minimal first-order axioms.

**Theorem (Badia, Cintula, Hájek and Tedder).** Let $\mathrm L_0$ be the propositional logic in the language $\to, \wedge, \vee, \bot$ (with $\neg\varphi = \varphi \to \bot$ and $\varphi \leftrightarrow \psi = (\varphi \to \psi) \wedge (\psi \to \varphi)$) given by the Hilbert system with the axioms $\varphi \to \varphi$, $\varphi \wedge \psi \to \varphi$, $\varphi \wedge \psi \to \psi$, $\varphi \to \varphi \vee \psi$, $\psi \to \varphi \vee \psi$ and the rules (premises before $\rhd$) weakening $\varphi \rhd \psi \to \varphi$, modus ponens $\varphi, \varphi \to \psi \rhd \psi$, assertion $\varphi \rhd (\varphi \to \psi) \to \psi$, transitivity $\varphi \to \psi, \psi \to \chi \rhd \varphi \to \chi$, De Morgan $\neg\varphi \vee \neg\psi \rhd \neg(\varphi \wedge \psi)$, $\chi \to \varphi, \chi \to \psi \rhd \chi \to \varphi \wedge \psi$ and $\varphi \to \chi, \psi \to \chi \rhd \varphi \vee \psi \to \chi$. Let $\mathrm{QL}_0$ be its first-order extension over the language with $0$, successor $S$, binary predicates $=$ and $\le$ and ternary predicates $A$ and $M$: the substitution instances of the axioms and rules of $\mathrm L_0$ together with $(\forall x)\varphi(x) \to \varphi(t)$, $\varphi(t) \to (\exists x)\varphi(x)$, $\chi \to \psi \rhd \chi \to (\forall x)\psi$ and $\psi \to \chi \rhd (\exists x)\psi \to \chi$ (for $t$ substitutable for $x$ and $x$ not free in $\chi$), and the equality axioms $x = x$, $x = y \to y = x$, $x = y \to (y = z \to x = z)$, $x = y \to t(x) = t(y)$ and $x = y \to (\varphi(x) \to \varphi(y))$. Write $\overline n$ for the numeral $S \cdots S(0)$ with $n$ occurrences of $S$. Let $\mathrm R^\sim$ be the theory with the following axioms, for all natural numbers $m, n$ and a variable $x$, where in the first two $m + n$ and $m \cdot n$ stand for the numerals of the sum and the product, and the third is for $m \neq n$:

$$
A(\overline m, \overline n, x) \leftrightarrow \overline{m + n} = x, \quad M(\overline m, \overline n, x) \leftrightarrow \overline{m \cdot n} = x, \quad \overline m \neq \overline n, \quad x \le \overline n \leftrightarrow \bigvee_{k \le n} x = \overline k, \quad x \le \overline n \vee \overline n \le x, \quad x \le \overline n \vee \neg(x \le \overline n).
$$

A theory is *consistent* in a logic if it proves no $\Sigma_1$-formula together with its negation ($\Sigma_1$-consistency, Section 2 of the source), and *essentially undecidable* in that logic if it is consistent and every consistent theory extending it in that logic is undecidable (Definition 2.2). Then $\mathrm R^\sim$ is essentially undecidable in $\mathrm{QL}_0$ (Theorem 4.10 of the source). Consequently, for every propositional logic expanding $\mathrm L_0$ and predicate logic expanding $\mathrm{QL}_0$, every theory extending $\mathrm R^\sim$ that does not prove both a $\Sigma_1$-formula and its negation is essentially undecidable (Corollary 4.11). Here a $\Sigma_1$-formula is one of the form $(\exists x)\psi$ with every quantifier of $\psi$ bounded, $(\forall x \le y)\varphi = (\forall x)(\neg(x \le y) \vee \varphi)$ and $(\exists x \le y)\varphi = (\exists x)(x \le y \wedge \varphi)$.

[Robinson's $\mathsf Q$](../../../first-order-logic/peano-arithmetic-and-robinson-s-q/qtheory.md) is essentially undecidable in intuitionistic logic, and Hájek proved essential undecidability of Grzegorczyk's relational variant $\mathsf Q^\sim$ in the fuzzy logic BL; the theorem weakens both the logic and the theory. In a stronger logic $\mathrm{QSL}_w$, $\mathsf Q^\sim$ is essentially undecidable (Corollary 6.16).

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof follows Kleene's structural form of Rosser's argument. A theory is *Rosser* in a logic if every pair of disjoint recursively enumerable sets is separated by a $\Sigma_1$-formula provable for members of one set and refutable for members of the other; a consistent Rosser theory is essentially undecidable (Theorem 2.5), because there are disjoint recursively enumerable sets that no recursive set separates. For $\mathrm R^\sim$ one shows soundness in the standard model, $\Sigma_1$-completeness for numerical instances (Theorem 4.8) and the separation property (Lemma 4.9), using only the rules of $\mathrm{QL}_0$.

## Sources

- G. Badia, P. Cintula, P. Hájek and A. Tedder, "How Much Propositional Logic Suffices for Rosser's Essential Undecidability Theorem?", *The Review of Symbolic Logic* 15(2):487–504, 2022 (published online 2020), <https://doi.org/10.1017/S175502032000012X>; numbers from arXiv:2006.12275v1, <https://arxiv.org/abs/2006.12275v1>: Section 1 (the axioms of $\mathrm R^\sim$ and $\mathsf Q^\sim$), Section 2 (Definitions 2.2 and 2.4, Theorem 2.5), Section 3 (the logic $\mathrm L_0$), Section 4 (the logic $\mathrm{QL}_0$, Theorems 4.8 and 4.10, Lemma 4.9, Corollary 4.11) and Corollary 6.16.
