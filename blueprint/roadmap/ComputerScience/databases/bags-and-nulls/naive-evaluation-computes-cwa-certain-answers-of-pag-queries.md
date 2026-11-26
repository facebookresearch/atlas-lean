# Naive evaluation computes closed-world certain answers of PAG queries

The naive evaluation $\mathrm{naive}(q, I)$ of a first-order query $q = \varphi(\bar x)$ on an incomplete instance
$I$ evaluates $\varphi$ on $I$ with nulls treated as values distinct from each other and from all constants (an equality
between two distinct nulls, or a null and a constant, is false), with $\bar x$ ranging over tuples from the domain of $I$
and the constants of $q$. The class PAG of positive formulae with atomic guards contains every atomic formula and is
closed under $\wedge$, $\vee$, $\exists x$, $\forall x$, and guarded implication $\forall \bar x\,(\alpha(\bar x) \to \varphi)$
where $\varphi$ is in PAG and the guard $\alpha(\bar x)$ is either a relational atom $R(x_1, \dots, x_n)$ whose positions
hold the distinct variables $\bar x = (x_1, \dots, x_n)$, with no constant and no repeated variable, or an equality
$x_1 = x_2$ between two distinct variables $\bar x = (x_1, x_2)$. A constant in the guard
breaks the theorem: on the instance with the single fact $R(\bot, b)$ and $S$ empty, $\forall x\, (R(a, x) \to S(x))$ is
naively true but false under the valuation $\bot \mapsto a$.

For every PAG query $q$ and incomplete instance $I$, $\mathrm{naive}(q, I) = \mathrm{cert}_{\mathrm{cwa}}(q, I)$. PAG
queries include relational division ("objects related to every listed object"). The equality fails for open-world
certain answers: the PAG query $\forall x \forall y \forall z\,(\mathrm{Person}(x, y, z) \to \exists u\,\mathrm{Profession}(x, u))$
can be naively and closed-world certainly true on an instance while its open-world certain answer is false, since an
added Person fact may lack a profession.

## Depends on

- [Open-world semantics and certain answers with nulls](open-world-semantics-and-certain-answers-with-nulls.md)

## Proof depends on

- [Naive evaluation is exact for queries preserved under homomorphisms](naive-evaluation-is-exact-for-homomorphism-preserved-queries.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Example 39.5 (pp. 370–371), Definition 40.3 and Theorem 40.4(2) (p. 379), and the proof completing Theorem 40.4 (p. 380).
- L. Libkin, "Certain answers as objects and knowledge", *Artificial Intelligence*, 2016, author copy <https://homepages.inf.ed.ac.uk/libkin/papers/aij.pdf>, p. 12 (the two forms of guard: $R(\bar x)$ with distinct universally bound variables in every position, and $x = y$ for distinct
bound variables).
