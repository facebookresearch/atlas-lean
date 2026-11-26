# Pure equilibria of potential games as local search

Consider games given with an exact potential $\Phi$ in the cost convention of the existing exact-potential page (a unilateral deviation changes
the deviator's cost and $\Phi$ by the same amount), where profiles have encodings of polynomial size whose validity is decidable in polynomial
time, $\Phi$ takes integer values of polynomial bit size and is computable in polynomial time, an initial profile is computable in polynomial
time, and the unilateral-deviation neighbourhood of a profile can be enumerated (or an improving neighbour found) in polynomial time. Then
the pure Nash equilibria are exactly the local minima of $\Phi$ under that neighbourhood, and the problem of finding one is in PLS, relative
to the external definition of PLS; congestion games with integer delays of polynomial bit size, through Rosenthal's potential, are an
instance.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: The class PLS.

## Depends on

- [Exact potential of a finite game](is-exact-potential-2.md)
- [Pure Nash equilibrium](is-pure-nash.md)
- [Equilibrium search problems](../equilibrium-search-problems.md)
- [Rosenthal's theorem](is-exact-potential-potential.md)

## Sources

- The Complexity of Pure Nash Equilibria — Fabrikant, Papadimitriou, Talwar, STOC 2004, Section 2 (definition of PLS; finding a pure Nash equilibrium of a congestion game is in PLS through Rosenthal's potential). <http://alex.fabrikant.us/papers/fpt04.pdf>
- Potential Games — Monderer and Shapley, Games and Economic Behavior 1996, Lemma 2.1 (equilibria coincide with those of the game whose payoffs are all the potential). <https://www.tau.ac.il/~mansour/sem-game-02-03/monderer-potential-96.pdf>
