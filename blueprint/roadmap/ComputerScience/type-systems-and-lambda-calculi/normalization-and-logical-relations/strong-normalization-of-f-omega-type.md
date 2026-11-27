# Strong normalization of F-omega type constructors

System $F_\omega$ is the system $\lambda\omega$ of the lambda cube: the pure type system with sorts $*$ and $\square$, axiom $* : \square$, and rules $(*, *)$, $(\square, *)$ and
$(\square, \square)$. A *constructor* of kind $K$ in a context $\Gamma$ is a term $A$ with $\Gamma \vdash A : K$ and $\Gamma \vdash K : \square$; the types are the constructors of kind $*$.

- **Strong normalization.** If $\Gamma \vdash A : B$ in $F_\omega$ then $A$ and $B$ are strongly normalizing: every $\beta$-reduction sequence starting from them is
  finite. In particular every well-kinded constructor is strongly normalizing under type-level $\beta$-reduction.

Together with the [Church–Rosser property of type-beta conversion](../system-f-2/type-beta-confluence-and-conversion-inversion/join.md), every well-kinded constructor has a unique $\beta$-normal form, and two well-kinded constructors are $\beta$-convertible, which is
the type equivalence used by the conversion rule, exactly when their normal forms coincide up to renaming of bound variables.

## Depends on

- [Church–Rosser property of type-beta conversion](../system-f-2/type-beta-confluence-and-conversion-inversion/join.md)
- [Intrinsically kinded Fω type operators](../system-f-2/intrinsically-kinded-type-operators-for-pure-f/ty.md)

## Sources

- H. P. Barendregt, "Introduction to generalized type systems", *Journal of Functional Programming* 1(2):125–154, 1991: Definition 2.1 and the table of rule pairs (the system $\lambda\omega$), Definition 2.2 (constructors and kinds), and Theorem 2.5 (strong normalization for the λ-cube). The normal-form consequence is derived on this page.
- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989 ( for $F_\omega$; its Chapter 14 treats System F).
