# Bimatrix games and the Lemke–Howson algorithm

A bimatrix game is a two-player game given by a payoff matrix for each player. The Lemke–Howson algorithm (1964) finds a Nash equilibrium by following a path of almost completely labelled vertex pairs of the two best-response polytopes from the artificial equilibrium $(0,0)$. In a nondegenerate game these vertex pairs form a graph whose vertices have degree one or two, so its path endpoints, the artificial equilibrium and the Nash equilibria, are even in number: a nondegenerate bimatrix game has an odd number of equilibria (von Stengel, *Algorithmic Game Theory*, Corollary 3.7). Papadimitriou abstracted this parity argument into the complexity class PPAD (*Algorithmic Game Theory*, Chapter 2, Section 2.4).

- [Expected payoffs in a bimatrix game](bilin-payoff.md)
- [Nash equilibrium of a bimatrix game](is-bimatrix-nash.md)
- [Pure best responses of player 1](best-responses.md)
- [Pure best responses of player 2](best-responses-2.md)
- [Nondegenerate bimatrix game](is-nondegenerate.md)
- [A nondegenerate bimatrix game has an odd number of Nash equilibria](odd-ncard-is-bimatrix-nash.md)

- [Correctness of support enumeration for bimatrix games](correctness-of-support-enumeration-for-bimatrix-games.md)
- [Abstract labeled-vertex graph for complementary pivoting](abstract-labeled-vertex-graph-for-complementary-pivoting.md)
- [Classification of Nash equilibria of 2×2 games](equilibria-of-two-by-two-games.md)

## Related topics

- [Nash's theorem](../nash-s-theorem/README.md): existence of equilibria in every finite game, proved from Brouwer's theorem; Lemke–Howson gives a combinatorial proof for two players.
- [PPAD and the END-OF-THE-LINE problem](../../../TheoryOfComputation/completeness-other-classes/ppad-and-the-end-of-the-line-problem/README.md): the complexity class abstracted from the Lemke–Howson argument; computing an approximate equilibrium of a bimatrix game is complete for it (Chen and Deng; Daskalakis, Goldberg and Papadimitriou 2009, Theorem 6.1).
- [Von Neumann's minimax theorem](../von-neumann-s-minimax-theorem/README.md): the zero-sum case, solvable by linear programming.
- [Correlated equilibria](../correlated-equilibria/README.md): in a nondegenerate two-player game the Nash equilibria are vertices of the correlated-equilibrium polytope (Papadimitriou, *Algorithmic Game Theory*, Theorem 2.5).
