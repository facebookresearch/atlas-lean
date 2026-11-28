# The ∀∀∀∃* consequences of the combined additive and multiplicative theory of the reals are r.e.-complete

The union of the complete theories of the real numbers as an additive structure and as a multiplicative structure, each with scalar multiplication by elements of a subfield $F$, has an undecidable set of consequences; its ∀∀∀∃* consequences in the language without scalars already form an r.e.-complete set.

**Theorem (Avigad and Friedman).** Let $F$ be any subfield of $\mathbb R$. Let $T_{\mathrm{add}}[F]$ be the first-order theory of $\mathbb R$ in the language $0, 1, +, -, <$ together with unary function symbols $f_a$ ($a \in F$) interpreted as $x \mapsto ax$, and $T_{\mathrm{mult}}[F]$ the first-order theory of $\mathbb R$ in the language $0, 1, \times, \div, <$ with the same symbols $f_a$, where $x \div 0 = 0$. Let $T[F] = T_{\mathrm{add}}[F] \cup T_{\mathrm{mult}}[F]$, and let $T[F]^*$ be the theory in the language $0, 1, +, \times, <$ with constants $c_a$ ($a \in F$) axiomatized by: $0, +, <$ is an ordered abelian group; $1, \times, <$ is a divisible ordered abelian group on the positive elements; $c_{a+b} = c_a + c_b$, $c_{ab} = c_a \times c_b$, and $0 < c_a$ for $0 < a$; $c_{a+b} \times x = c_a \times x + c_b \times x$ and $c_a \times (x + y) = c_a \times x + c_a \times y$. Then

- the set of sentences in the language $0, 1, +, \times, <$ (no constants $c_a$) provable in $T[F]^*$, and the set of sentences in the language $0, 1, +, -, \times, \div, <$ (no symbols $f_a$) provable in $T[F]$, are undecidable;
- in fact, the set of provable sentences of the form $\forall\forall\forall\exists^*$ in either case is r.e.-complete.

This is Theorem 11.9 of the source, proved by reducing solvability of Diophantine equations over the positive integers (Hilbert's tenth problem) through a model of $T[F]^*$ in which a definable set of reals coincides with the positive integers (Theorem 11.7 and Corollary 11.8 there).

By contrast, the universal fragment of $T[F]$ is decidable for every sufficiently computable $F$ (Theorem 7.3 of the source), and the three component theories $T_{\mathrm{add}}[F]$, $T_{\mathrm{mult}}[F]$ and their intersection admit quantifier elimination.

## Depends on

- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof constructs nonstandard models of $T[F]^*$ on the real line by twisting the multiplication with suitable bijections $h$ of $\mathbb R$ that fix the additive structure (Sections 9 to 11). For a model $M$ with elements $\mu, \kappa, \lambda$, property $(\ast)$ says that the set of $x$ with $1 \le x \le \mu$ and $(\kappa + x)(\lambda + x) = \kappa\lambda + \kappa x + \lambda x + x^2$ contains $1$ and is closed under $x \mapsto x + 1$ within $[1, \mu]$; property $(\ast\ast)$ says that this set is exactly the positive integers of $M$. Theorem 11.7 builds a model with property $(\ast\ast)$, so a Diophantine equation $D$ is solvable in positive integers iff in every model with property $(\ast)$ it is solvable over that set (Corollary 11.8). This statement is expressible as a $\forall\forall\forall\exists^*$ sentence of the language $0, 1, +, \times, <$, which reduces solvability of Diophantine equations over the positive integers, an r.e.-complete problem by the Davis–Putnam–Robinson–Matiyasevich theorem, to provability in $T[F]^*$ and, via the translations of Lemmas 4.1 and 4.2, in $T[F]$.

## Sources

- J. Avigad and H. Friedman, "Combining decision procedures for the reals", *Logical Methods in Computer Science* 2(4), 2006, paper 4, pp. 1–42, <https://doi.org/10.2168/LMCS-2(4:4)2006>; numbers from arXiv:cs/0601134v4, <https://arxiv.org/abs/cs/0601134v4>: Section 4 (the theories $T[F]$ and $T[F]^*$, Lemmas 4.1 and 4.2), Theorem 7.3, Theorem 11.7, Corollary 11.8 and Theorem 11.9.
