# λc-models

A *λc-model* is a category $\mathcal{C}$ with finite products, a [strong monad](strong-monads.md) $(T, \eta, \mu, t)$ satisfying the mono requirement, and a *$T$-exponential*
$(TB)^A$ for all objects $A$, $B$: an object with an isomorphism $\mathcal{C}_T(C \times A, B) \cong \mathcal{C}(C, (TB)^A)$ natural in $C$, where $\mathcal{C}_T$ is the
[Kleisli category](kleisli-triples-and-kleisli-categories.md). In call-by-value a procedure of type $A \to B$ is interpreted in $(TB)^A$, and in call-by-name in $(TB)^{TA}$; both
need only exponentials of this form. The notion generalizes partial cartesian closed categories, each of which can be viewed as a λc-model.

## Depends on

- [Strong monads](strong-monads.md)
- [Kleisli triples and Kleisli categories](kleisli-triples-and-kleisli-categories.md)

## Sources

- E. Moggi, "Notions of computation and monads", *Information and Computation* 93(1):55–92, 1991, <https://doi.org/10.1016/0890-5401(91)90052-4>: Section 3.1, the discussion of calling mechanisms before Definition 3.9, Definition 3.9 (λc-model) and Remark 3.10.
