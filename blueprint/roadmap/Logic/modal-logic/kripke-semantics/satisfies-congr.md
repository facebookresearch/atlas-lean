# Truth depends only on the visible part of the valuation

Let $M$ and $N$ be Kripke models on the same worlds with the same accessibility relation, and let
$U$ be a set of worlds closed under the relation (if $v \in U$ and $v R u$, then $u \in U$).
If, at every world of $U$, the valuations of $M$ and $N$ agree on every atom occurring in
$\varphi$, then $M, v \models \varphi \iff N, v \models \varphi$ for every $v \in U$.

Taking for $U$ the set of worlds reachable from $w$ shows that truth at $w$ depends only on the
generated submodel at $w$.

## Informally uses

- [Satisfaction in a Kripke model](satisfies.md): the induction on $\varphi$
  follows its clauses.

## Background

- [Atoms of a modal formula](../sahlqvist-formulas/atoms.md): the atoms on which the valuations
  must agree.

## Sources

- P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001
  (invariance of truth under generated submodels).
