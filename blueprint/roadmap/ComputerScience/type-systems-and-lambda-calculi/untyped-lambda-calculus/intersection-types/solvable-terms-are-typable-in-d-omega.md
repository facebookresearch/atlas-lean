# Solvable terms are the terms typable with a non-trivial intersection type

An untyped λ-term $t$ is solvable if and only if $\Gamma \vdash_{D\Omega} t : A$ for some context $\Gamma$ and some non-trivial type $A$ of
[system DΩ](intersection-type-system-d-omega.md). In particular, if $t$ has a non-trivial type in DΩ then the head reduction of $t$ is finite (the head normal form
theorem), and every head normal form has a type of the form $U_1 \to (\cdots \to (U_n \to X) \cdots)$ with $X$ a type variable.

## Depends on

- [The intersection type system DΩ](intersection-type-system-d-omega.md)
- [Head normal forms and solvable terms](../solvability-and-bohm-s-theorem/head-normal-forms-and-solvable-terms.md)

## Proof depends on

- [Subject reduction and subject expansion for intersection types](subject-reduction-and-expansion-for.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 3, Theorem 3.7 (head normal form theorem) and Proposition 3.21; Chapter 4, Theorem 4.9 (equivalence of solvability, a head normal form, finite head reduction and typability with a non-trivial type in DΩ).
