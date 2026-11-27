# β-normal terms are typable in system D

Every β-normal untyped term $t$ is typable in [system D](intersection-type-system-d.md): there are a context $\Gamma$ and a type $A$ with $\Gamma \vdash_D t : A$. If moreover $t$ does
not start with $\lambda$, then for every type $A$ there is such a context. The proof combines typings with the fact that for any typings $\Gamma \vdash_D t : A$ and
$\Gamma' \vdash_D u : B$ there is one context $\Gamma''$ in which both hold: it declares a variable declared in both with the intersection of its two types, and keeps a variable declared in
only one of them with its type there.

## Depends on

- [The intersection type system D](intersection-type-system-d.md)
- [β-reduction](../beta-reduction-and-confluence/beta-reduction.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 3, Propositions 3.23 and 3.24.
