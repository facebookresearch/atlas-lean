# Böhm transformations

A *Böhm transformation* is a map on untyped λ-terms obtained by composing finitely many elementary maps $B_{u} : t \mapsto t\, u$ and $B_{u,x} : t \mapsto t[u/x]$, for
fixed terms $u$ and variables $x$. Every Böhm transformation $F$ is compatible with β- and with βη-conversion: $t =_\beta t'$ implies $F(t) =_\beta F(t')$, and likewise for
$=_{\beta\eta}$. For every Böhm transformation $F$ there are terms $t_1, \dots, t_k$ with $F(t) = t\, t_1 \cdots t_k$ for every closed term $t$; they are built from the terms
$u$ of the elementary maps, so they are closed when all of those are.

## Depends on

- [β-reduction](../beta-reduction-and-confluence/beta-reduction.md)
- [η-reduction and βη-conversion](../beta-reduction-and-confluence/eta-reduction-and-beta-eta-conversion.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 5, the definition of Böhm transformations and Lemma 5.5, with the reduction from Theorem 5.6 to Theorem 5.2.
