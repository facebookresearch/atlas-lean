# Kleisli triples and Kleisli categories

A *Kleisli triple* over a category $\mathcal{C}$ is a triple $(T, \eta, (-)^*)$ of a map $T$ on objects, morphisms $\eta_A : A \to TA$ and, for every $f : A \to TB$, a morphism
$f^* : TA \to TB$, such that (writing $;$ for diagrammatic composition)

- $\eta_A^* = \mathrm{id}_{TA}$;
- $\eta_A ; f^* = f$ for $f : A \to TB$;
- $f^* ; g^* = (f ; g^*)^*$ for $f : A \to TB$ and $g : B \to TC$.

It satisfies the *mono requirement* if every $\eta_A$ is a monomorphism. Its *Kleisli category* $\mathcal{C}_T$ has the objects of $\mathcal{C}$, morphisms
$\mathcal{C}_T(A, B) = \mathcal{C}(A, TB)$, identities $\eta_A$, and composite $f ; g^*$ of $f : A \to TB$ and $g : B \to TC$. Read $TA$ as computations of type $A$, $\eta_A$ as the
inclusion of values and $f^*$ as "evaluate, then apply $f$"; examples in sets are partiality $TA = A + \{\bot\}$, nondeterminism $TA = \mathcal{P}_{\mathrm{fin}}(A)$, side effects
$TA = (A \times S)^S$, exceptions $TA = A + E$ and continuations $TA = R^{(R^A)}$.

## Depends on

- [Category](../../../../CategoryTheory/categories-and-functors/category.md)

## Sources

- E. Moggi, "Notions of computation and monads", *Information and Computation* 93(1):55–92, 1991, <https://doi.org/10.1016/0890-5401(91)90052-4>: Section 1, Example 1.1, Definitions 1.2 and 1.3, and Example 1.4.
