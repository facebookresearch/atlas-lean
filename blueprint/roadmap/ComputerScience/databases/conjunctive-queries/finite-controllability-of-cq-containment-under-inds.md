# Finite controllability of conjunctive-query containment under inclusion dependencies

For a set $\Sigma$ of integrity constraints and conjunctive queries $q, q'$, write $q \subseteq_\Sigma q'$ when
$q(D) \subseteq q'(D)$ for every (finite) database $D$ that satisfies $\Sigma$. Write $q \subseteq^\infty_\Sigma q'$ when $q(D) \subseteq q'(D)$ for every possibly infinite
database $D$ that satisfies $\Sigma$, with answers on infinite databases defined by assignments as for finite ones. For
conjunctive queries $q, q'$ over a schema and a set $\Sigma$ of inclusion dependencies over it with nonempty attribute sequences,
$q \subseteq_\Sigma q'$ if and only if $q \subseteq^\infty_\Sigma q'$. Every inclusion dependency here has nonempty attribute sequences ($k \ge 1$), as in the cited definition. The [linked
syntax](../dependencies-and-the-chase/ind.md) also allows arity zero, where $R[\,] \subseteq S[\,]$ says that $S$ is nonempty whenever $R$ is; such
dependencies are excluded.

## Expansion

This node states a precise result that the cited textbook states without proof. A good expansion locates and checks
a published proof and cites it with its locator under `## Sources`.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)
- [Satisfaction of an inclusion dependency](../dependencies-and-the-chase/inclusion-dependencies-and-finite-implication.md)
- [Syntax of an inclusion dependency](../dependencies-and-the-chase/ind.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 11.2 with $k \ge 1$ (pp. 77–78), Definition 17.7 and Theorem 17.10 (p. 136); the textbook states the theorem without proof.
