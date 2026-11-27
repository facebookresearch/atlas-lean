# Kleisli triples correspond to monads

Over any category $\mathcal{C}$ there is a one-to-one correspondence between [Kleisli triples](kleisli-triples-and-kleisli-categories.md) and monads $(T, \eta, \mu)$ (an endofunctor
with natural transformations $\eta : \mathrm{Id} \to T$ and $\mu : T^2 \to T$ satisfying the associativity and unit laws). A Kleisli triple $(T, \eta, (-)^*)$ gives the monad with
$T(f) = (f ; \eta_B)^*$ for $f : A \to B$ and $\mu_A = \mathrm{id}_{TA}^*$; a monad gives the Kleisli triple with $f^* = T(f) ; \mu_B$ for $f : A \to TB$.

## Depends on

- [Kleisli triples and Kleisli categories](kleisli-triples-and-kleisli-categories.md)
- [Functor](../../../../CategoryTheory/categories-and-functors/functor.md)
- [Natural transformation](../../../../CategoryTheory/categories-and-functors/natural-transformation.md)

## Sources

- E. Moggi, "Notions of computation and monads", *Information and Computation* 93(1):55–92, 1991, <https://doi.org/10.1016/0890-5401(91)90052-4>: Section 1, Definition 1.5 (monad) and Proposition 1.6 with its proof.
