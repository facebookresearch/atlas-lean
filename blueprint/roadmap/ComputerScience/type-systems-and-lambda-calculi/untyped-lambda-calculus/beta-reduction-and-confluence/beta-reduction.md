# β-reduction

On untyped λ-terms, taken up to α-equivalence, *one-step β-reduction* $\to_\beta$ is the least relation such that $(\lambda x.\, P)\, Q \to_\beta P[x := Q]$
(capture-avoiding substitution) and that is compatible with the term formers: if $P \to_\beta P'$ then $\lambda x.\, P \to_\beta \lambda x.\, P'$, $P\, Z \to_\beta P'\, Z$ and
$Z\, P \to_\beta Z\, P'$ for all terms $Z$. A term $(\lambda x.\, P)\, Q$ is a *β-redex* and $P[x := Q]$ its *contractum*.

- *Multi-step β-reduction* $\twoheadrightarrow_\beta$ is the reflexive–transitive closure of $\to_\beta$, and *β-conversion* $=_\beta$ its reflexive–symmetric–transitive
  closure; β-conversion is the β-equivalence of the [untyped term model](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md).
- A term is a *β-normal form* if no term is one step from it; it is *β-normalizable* if it reduces to a β-normal form, and *strongly β-normalizing*
  if there is no infinite sequence $M = M_0 \to_\beta M_1 \to_\beta \cdots$.

For example $(\lambda x.\, x\, x)(\lambda z.\, z) \twoheadrightarrow_\beta \lambda y.\, y$, while $\Omega = (\lambda x.\, x\, x)(\lambda x.\, x\, x) \to_\beta \Omega$ has an infinite reduction sequence. If
$M \to_\beta M'$ then every free variable of $M'$ is free in $M$, and $\twoheadrightarrow_\beta$ is preserved by substitution: if $M \twoheadrightarrow_\beta M'$ and $N \twoheadrightarrow_\beta N'$ then
$M[x := N] \twoheadrightarrow_\beta M'[x := N']$.

## Depends on

- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)
- [Beta equivalence in the untyped term model](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md)
- [Abstract reduction system](../../../../Logic/first-order-logic/term-rewriting/abstract-reduction-system.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definitions 1.2.1 and 1.2.2 and Example 1.2.4; Section 1.3 for $\Omega$.
- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 1, Section 3, the definitions of $\beta_0$ and $\beta$, Propositions 1.20–1.23 (substitution and compatibility) and the definition of normal and normalizable terms.
