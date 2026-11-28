# Strong monads

A *strong monad* over a category $\mathcal{C}$ with chosen finite products is a monad $(T, \eta, \mu)$ together with a natural transformation
$t_{A,B} : A \times TB \to T(A \times B)$, the *tensorial strength*, such that

- $t_{1,A} ; T(r_A) = r_{TA}$, where $r_A : 1 \times A \to A$ is the canonical isomorphism;
- $t_{A \times B, C} ; T(\alpha_{A,B,C}) = \alpha_{A,B,TC} ; (\mathrm{id}_A \times t_{B,C}) ; t_{A, B \times C}$, where $\alpha$ is the associativity isomorphism;
- $(\mathrm{id}_A \times \eta_B) ; t_{A,B} = \eta_{A \times B}$;
- $(\mathrm{id}_A \times \mu_B) ; t_{A,B} = t_{A, TB} ; T(t_{A,B}) ; \mu_{A \times B}$.

The strength lets a computation use a value from its context: it interprets sequencing $\mathrm{let}\ x \Leftarrow e_1\ \mathrm{in}\ e_2$ when $e_2$ has other free variables. All
monads of the examples in sets (partiality, nondeterminism, side effects, exceptions, continuations) are strong.

## Depends on

- [Kleisli triples correspond to monads](kleisli-triples-correspond-to-monads.md)
- [Terminal object](../../../../CategoryTheory/limits-and-colimits/shapes-of-limits/terminal-object.md)

## Sources

- E. Moggi, "Notions of computation and monads", *Information and Computation* 93(1):55–92, 1991, <https://doi.org/10.1016/0890-5401(91)90052-4>: Section 3, Remark 3.1, Definition 3.2, Remark 3.3 and Example 3.5.
