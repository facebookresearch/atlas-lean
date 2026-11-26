# Two-player Nash equilibrium is in PPAD

The search problem of finding an exact rational Nash equilibrium of a two-player game with rational payoffs is polynomial-time reducible to END-OF-THE-LINE, and therefore belongs to PPAD.

## Proof sketch

Normalize payoffs to positive integers and apply the integer perturbation. Encode each basis pair of the perturbed best response polytopes as a bit string; Lemke–Howson pivoting computes neighbours in polynomial time and Shapley's index orients edges, giving successor and predecessor circuits. The artificial equilibrium becomes the standard source, and every other degree-one node yields an exact equilibrium.

## Depends on

- [Exact rational Nash equilibria of bimatrix games are polynomially verifiable](exact-rational-nash-equilibria-of-bimatrix-games-are-polynomially-verifiable.md)
- [END-OF-THE-LINE is total](../../../../TheoryOfComputation/completeness-other-classes/ppad-and-the-end-of-the-line-problem/exists-solution.md)
- [Equilibrium search problems](../../equilibrium-search-problems.md)

## Proof depends on

- [Shapley's orientation of Lemke–Howson paths](shapleys-orientation-of-lemke-howson-paths.md)
- [Integer perturbation of best response polytopes recovers exact rational equilibria](integer-perturbation-of-best-response-polytopes-recovers-exact-rational-equilibr.md)
- [Degree structure of the Lemke–Howson graph](degree-structure-of-the-lemke-howson-graph.md)

## Sources

- Christos H. Papadimitriou, "On the Complexity of the Parity Argument and Other Inefficient Proofs of Existence", Journal of Computer and System Sciences, 1994.
- Lloyd S. Shapley, "A Note on the Lemke–Howson Algorithm", Pivoting and Extensions, Springer Berlin Heidelberg, 1974.
- Carlton E. Lemke and Joseph T. Howson Jr., "Equilibrium Points of Bimatrix Games", Journal of the Society for Industrial and Applied Mathematics, 1964.
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
