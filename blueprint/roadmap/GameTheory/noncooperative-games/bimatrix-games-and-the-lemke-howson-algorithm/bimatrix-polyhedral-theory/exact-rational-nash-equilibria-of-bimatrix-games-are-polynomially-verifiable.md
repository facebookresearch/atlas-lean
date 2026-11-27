# Exact rational Nash equilibria of bimatrix games are polynomially verifiable

Encode a two-player game with rational payoffs in binary. Every such game with nonempty strategy sets has a Nash equilibrium with rational probabilities whose bit length is bounded by a polynomial in the input length $L$, and the relation "$w$ encodes such an equilibrium of the game encoded by $c$" is decidable in polynomial time. Hence finding a rational Nash equilibrium of a bimatrix game is a total search problem in TFNP.

## Proof sketch

Existence of a short equilibrium follows from vertex enumeration: equilibria of the perturbed nondegenerate game are vertices, whose coordinates are ratios of determinants, so their bit length is polynomial in $L$ (von Stengel, Section 3.5). Verification clears denominators and checks the finitely many best-response inequalities in integer arithmetic.

## Depends on

- [Nash equilibrium of a bimatrix game](../is-bimatrix-nash.md)
- [Search problems: FNP, FP and TFNP](../../../../TheoryOfComputation/complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)
- [Explicit encoding and size of finite games](../../explicit-encoding-and-size-of-finite-games.md)

## Proof depends on

- [Integer perturbation of best response polytopes recovers exact rational equilibria](integer-perturbation-of-best-response-polytopes-recovers-exact-rational-equilibr.md)
- [A nondegenerate bimatrix game has an odd number of Nash equilibria](../odd-ncard-is-bimatrix-nash.md)

## Sources

- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007, Section 3.5.
- Christos H. Papadimitriou, "On the Complexity of the Parity Argument and Other Inefficient Proofs of Existence", Journal of Computer and System Sciences, 1994.
