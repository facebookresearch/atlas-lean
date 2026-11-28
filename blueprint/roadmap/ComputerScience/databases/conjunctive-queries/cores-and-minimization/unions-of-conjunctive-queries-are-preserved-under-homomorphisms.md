# Unions of conjunctive queries are preserved under homomorphisms

Let $q = \varphi(\bar x)$ be a $k$-ary union of conjunctive queries in which the disjuncts may also contain equality
atoms $y = a$ between a variable and a constant, and let $C$ be the set of constants occurring in $\varphi$. For databases
$D, D'$ and tuples $\bar a \in \mathrm{Dom}(D)^k$, $\bar b \in \mathrm{Dom}(D')^k$, write $(D, \bar a) \to_C (D', \bar b)$
when some map $h : \mathrm{Dom}(D) \to \mathrm{Dom}(D')$ that is the identity on $C \cap \mathrm{Dom}(D)$ sends every fact of
$D$ to a fact of $D'$ and satisfies $h(\bar a) = \bar b$. Then $q$ is preserved under homomorphisms:

$$(D, \bar a) \to_C (D', \bar b) \text{ and } \bar a \in q(D) \implies \bar b \in q(D').$$

For Boolean first-order queries without constants the converse holds on finite structures with nonempty universe: such a
query preserved under homomorphisms is equivalent to an existential-positive sentence (Rossman's homomorphism preservation
theorem). An existential-positive sentence is a union of conjunctive queries or one of the two trivial sentences; the
unsatisfiable sentence $\exists x\, \neg(x = x)$ is preserved under homomorphisms, but no union of conjunctive queries as defined
here, with at least one disjunct of at least one atom, is equivalent to it. The source's
Theorem 28.11 states the converse also for queries with constants, without proof; with answer tuples drawn only from
$\mathrm{Dom}(D)$, as in the test above, it fails there: $\varphi(x) = (x = c \wedge \neg R(c))$ passes the test, since no tuple
of the active domain witnesses a violation, but returns $c$ on the empty database and not after adding $R(c)$.

## Depends on

- [Answers of a conjunctive query](../answers-of-a-conjunctive-query.md)
- [Containment of unions of conjunctive queries](containment-of-unions-of-conjunctive-queries.md)

## Proof depends on

- [Conjunctive queries are preserved under homomorphisms](../conjunctive-queries-are-preserved-under-homomorphisms.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 28.10 and the discussion of Theorem 28.11 (pp. 257–258).
- B. Rossman, "Homomorphism preservation theorems", *Journal of the ACM* 55(3), Article 15, 2008, Theorem 1.7 (p. 3) and §2.1 (structures with nonempty universe).
