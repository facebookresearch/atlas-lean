# Explicit encoding and size of finite games

A finite game is given explicitly by the number $n$ of players, the strategy sets and, for every player and every strategy profile, a
rational payoff in binary; its size is the total bit length. Bimatrix games are the case $n = 2$. Succinct representations (graphical,
polymatrix, congestion, action-graph games) have their own size measures, and complexity statements name the encoding. For results on
correlated equilibria of succinct games, two assumptions are stated explicitly: polynomial type (the numbers of players and of
strategies per player are polynomial in the representation size) and the polynomial expectation property (each player's expected
utility under a product distribution can be computed in time polynomial in the representation size and in the bit size of the
distribution). The source bounds that time by the representation size alone; the bit size of the distribution is included here
because the algorithm must read the distribution.

## Expansion

This node states a precise definition.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Finite normal-form (strategic) game.
- Statement prerequisite: Algorithm cost model.

## Sources

- A. X. Jiang and K. Leyton-Brown, *Polynomial-time Computation of Exact Correlated Equilibrium in Compact Games* (arXiv:1011.0253v1; Games Econ. Behav. 2015), §2 (the polynomial-type and polynomial-expectation assumptions, following Papadimitriou and Roughgarden). <https://arxiv.org/pdf/1011.0253>
- Computing Correlated Equilibria in Multi-Player Games — Papadimitriou and Roughgarden. <https://ranger.uta.edu/~weems/NOTES6319/PAPERSONE/papadimitriou.pdf> Background reference.
