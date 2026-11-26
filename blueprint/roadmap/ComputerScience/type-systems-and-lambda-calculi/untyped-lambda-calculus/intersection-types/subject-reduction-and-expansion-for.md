# Subject reduction and subject expansion for intersection types

Let $\vdash$ be the typing judgment of [system D](intersection-type-system-d.md) or of [system DΩ](intersection-type-system-d-omega.md).

- **Subject reduction.** If $\Gamma \vdash t : A$ and $t$ β-reduces to $t'$ in any number of steps, then $\Gamma \vdash t' : A$.
- **Subject expansion in DΩ.** If $t$ β-reduces to $t'$ and $\Gamma \vdash_{D\Omega} t' : A$, then $\Gamma \vdash_{D\Omega} t : A$. Hence if $t \simeq_\beta t'$, then $\Gamma \vdash_{D\Omega} t : A$
  holds exactly when $\Gamma \vdash_{D\Omega} t' : A$ does: types in DΩ are invariant under β-conversion.
- **Failure of expansion in D.** Subject expansion fails for system D: $\lambda y.\, (\lambda x.\, y)(y\, y)$ β-reduces to $\lambda y.\, y$, which has type $Y \to Y$ in D, but
  $\lambda y.\, (\lambda x.\, y)(y\, y)$ does not.

## Depends on

- [Beta equivalence in the untyped term model](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md)
- [The intersection type system D](intersection-type-system-d.md)
- [The intersection type system DΩ](intersection-type-system-d-omega.md)
- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)
- [β-reduction](../beta-reduction-and-confluence/beta-reduction.md)

## Proof depends on

- [Typing substituted terms with intersections](typing-substituted-terms-with-intersections.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 4, Proposition 4.1 (substitution), Proposition 4.3 (subject reduction, for D and DΩ), Corollary 4.5, Theorems 4.6 and 4.7 (subject expansion and invariance under β-conversion in DΩ), and Remark 1 after Corollary 4.18 (failure of expansion in D).
