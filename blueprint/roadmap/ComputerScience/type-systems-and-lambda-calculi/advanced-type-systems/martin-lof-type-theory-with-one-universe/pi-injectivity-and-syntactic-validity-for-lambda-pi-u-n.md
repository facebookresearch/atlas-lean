# Π-injectivity and syntactic validity for λΠUN

In [λΠUN](the-type-theory-lambda-pi-u-n.md):

1. (Π-injectivity) if $\Gamma \vdash \Pi\, F\, G = \Pi\, H\, E$ then $\Gamma \vdash F = H$ and $\Gamma.F \vdash G = E$;
2. (syntactic validity) if $\Gamma \vdash A = B$ then $\Gamma \vdash A$ and $\Gamma \vdash B$; if $\Gamma \vdash t : A$ then $\Gamma \vdash A$; if $\Gamma \vdash t = u : A$ then $\Gamma \vdash t : A$ and $\Gamma \vdash u : A$;
3. (syntactic inequality) distinct type formers are not convertible: for $A$ and $B$ among $\mathsf{U}$, $\mathsf{N}$, a neutral type and a Π-type, with different head forms,
   $\Gamma \vdash A = B$ does not hold.

Π-injectivity is the property that a direct syntactic proof of subject reduction would need; here it follows from the fundamental theorem of the logical relation.

## Depends on

- [The type theory λΠUN](the-type-theory-lambda-pi-u-n.md)

## Expansion

This page becomes ready once:

- The Kripke logical relation of reducibility for λΠUN, its fundamental theorem and the corollary that every well-formed object is reducible (Theorem 3.21 and Corollary 3.22 of the source) (proof prerequisite; not yet stated)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 3.6, Theorem 3.25 (Π-injectivity), Theorem 3.26 (syntactic validity) and Theorem 3.30 (syntactic inequality).
