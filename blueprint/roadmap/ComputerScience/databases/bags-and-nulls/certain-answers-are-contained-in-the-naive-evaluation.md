# Certain answers are contained in the naive evaluation

The naive evaluation $\mathrm{naive}(q, I)$ of a first-order query $q = \varphi(\bar x)$ on an incomplete instance
$I$ evaluates $\varphi$ on $I$ with nulls treated as values distinct from each other and from all constants (an equality
between two distinct nulls, or a null and a constant, is false), with $\bar x$ ranging over tuples from the domain of $I$
and the constants of $q$.

For every first-order query $q$ and incomplete instance $I$,
$\mathrm{cert}_{\mathrm{owa}}(q, I) \subseteq \mathrm{cert}_{\mathrm{cwa}}(q, I) \subseteq \mathrm{naive}(q, I)$.
The second inclusion can be strict: for $\varphi(x) = R(x) \wedge \neg S(x)$ on the instance with facts $R(1)$ and
$S(\bot)$, naive evaluation returns $1$ while the closed-world certain answers are empty.

## Depends on

- [Open-world semantics and certain answers with nulls](open-world-semantics-and-certain-answers-with-nulls.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 40.1 and Proposition 40.2 with the example following it (p. 378).
