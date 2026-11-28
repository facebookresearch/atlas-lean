# Diophantine sentences over the natural numbers with prefix ∃∃∀∃ are undecidable

There is no algorithm that decides, for an arbitrary polynomial $f(u, v, x, y)$ with integer coefficients, whether the sentence $\exists u \, \exists v \, \forall x \, \exists y \; f(u, v, x, y) = 0$ holds with all variables ranging over the natural numbers.

Let $\mathbb{N} = \{0, 1, 2, \dots\}$. For a polynomial $f \in \mathbb{Z}[u, v, x, y]$ consider the sentence

$$
\exists u \in \mathbb{N} \; \exists v \in \mathbb{N} \; \forall x \in \mathbb{N} \; \exists y \in \mathbb{N} \quad f(u, v, x, y) = 0 .
$$

**Theorem (Matiyasevich–Robinson).** There is no algorithm that decides, for an arbitrary $f \in \mathbb{Z}[u, v, x, y]$, whether this sentence is true.

Conventions: the quantifier prefix $\exists\exists\forall\exists$, with exactly four variables in this order, is fixed and the polynomial is the input; all variables range over $\mathbb{N}$.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

By the Davis–Putnam–Robinson–Matiyasevich theorem there is a recursively enumerable set $A \subseteq \mathbb{N}$ that is not recursive and is Diophantine. Matiyasevich and Robinson gave universal representations of recursively enumerable sets with three quantifiers in front of a single polynomial equation, which yield the prefix $\exists\exists\forall\exists$ for such sets; Jones's classification of quantifier prefixes over Diophantine equations records this case. Substituting each fixed $a$ into a representation of $A$ yields a sentence of the stated form, and an algorithm deciding these sentences would decide membership in $A$. A good expansion links a page for the Matiyasevich–Robinson universal three-quantifier representation, from which the prefix $\exists\exists\forall\exists$ follows.

## Sources

- J. Maurice Rojas, *On the complexity of Diophantine geometry in low dimensions*, in: Proceedings of the 31st Annual ACM Symposium on Theory of Computing (STOC 1999), ACM, 1999, pp. 527–536, https://doi.org/10.1145/301250.301395, read in the copy arXiv:math/9811088v1, where the statement is recalled as established, with references to Matiyasevich and Robinson and to Jones, in the subsection "Dimensions One and Two" of the introduction.
- Yu. V. Matiyasevich and Julia Robinson, *Two universal 3-quantifier representations of recursively enumerable sets* (in Russian), in: Teoriya Algorifmov i Matematicheskaya Logika (volume dedicated to A. A. Markov), Vychislitel'nyi Tsentr Akademii Nauk SSSR, Moscow, 1974, pp. 112–123 (no DOI), cited beside the source above.
- J. P. Jones, *Classification of quantifier prefixes over Diophantine equations*, Z. Math. Logik Grundlag. Math. 27 (1981), no. 25–30, 403–410, https://doi.org/10.1002/malq.19810272504, cited beside the source above.
