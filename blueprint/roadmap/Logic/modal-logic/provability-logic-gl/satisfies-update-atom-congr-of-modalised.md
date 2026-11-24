# A modalised atom is read only at visible worlds

Let $p$ be modalised in $\varphi$, let $M$ be a Kripke model and $w$ a world, and let $U$ be a set
of worlds closed under the relation and containing every successor of $w$. If two sets of worlds
$S$ and $S'$ agree on $U$, then
$M[p \mapsto S], w \models \varphi \iff M[p \mapsto S'], w \models \varphi$.

Proof: induction on $\varphi$. Unboxed occurrences are atoms other than $p$; a boxed subformula is
evaluated at successors of $w$, which lie in $U$, where locality applies.

## Informally uses

- [Truth depends only on the visible part of the valuation](../kripke-semantics/satisfies-congr.md)

## Background

- [Atom occurring only under a box](modalised.md)
- [Kripke model with one atom reinterpreted](../kripke-semantics/update-atom.md)
