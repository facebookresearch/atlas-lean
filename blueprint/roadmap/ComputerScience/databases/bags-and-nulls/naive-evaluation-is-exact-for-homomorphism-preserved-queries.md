# Naive evaluation is exact for queries preserved under homomorphisms

The naive evaluation $\mathrm{naive}(q, I)$ of a first-order query $q = \varphi(\bar x)$ on an incomplete instance
$I$ evaluates $\varphi$ on $I$ with nulls treated as values distinct from each other and from all constants (an equality
between two distinct nulls, or a null and a constant, is false), with $\bar x$ ranging over tuples from the domain of $I$
and the constants of $q$. A query $q$ is preserved under homomorphisms if $\bar a \in q(D)$ implies $\bar b \in q(D')$
whenever some map fixing the constants of $q$ sends the facts of $D$ to facts of $D'$ and $\bar a$ to $\bar b$; it is
preserved under strong onto homomorphisms if this holds for such maps that send the facts of $D$ onto exactly the facts
of $D'$.

Let $q$ be a first-order query and $I$ an incomplete instance. If $q$ is preserved under homomorphisms, then
$\mathrm{naive}(q, I) = \mathrm{cert}_{\mathrm{owa}}(q, I)$. If $q$ is preserved under strong onto homomorphisms, then
$\mathrm{naive}(q, I) = \mathrm{cert}_{\mathrm{cwa}}(q, I)$.

## Depends on

- [Open-world semantics and certain answers with nulls](open-world-semantics-and-certain-answers-with-nulls.md)

## Proof depends on

- [Certain answers are contained in the naive evaluation](certain-answers-are-contained-in-the-naive-evaluation.md)

## Related topics

- [Conjunctive queries are preserved under homomorphisms](../conjunctive-queries/conjunctive-queries-are-preserved-under-homomorphisms.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the definitions of preservation under (strong onto) homomorphisms and Proposition 40.5 (pp. 379–380).
