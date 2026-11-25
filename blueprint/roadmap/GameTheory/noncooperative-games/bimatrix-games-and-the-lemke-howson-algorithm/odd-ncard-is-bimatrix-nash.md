# A nondegenerate bimatrix game has an odd number of Nash equilibria

Let $M$ and $N$ be finite sets of pure strategies of players 1 and 2, and let $\Delta(M)$ and $\Delta(N)$ be their sets of mixed strategies (probability vectors).
If both players have at least one pure strategy and the game $(A, B)$ is nondegenerate, then the set of Nash
equilibria $(x, y) \in \Delta(M) \times \Delta(N)$ is finite and has odd cardinality.

## Remarks

- Both hypotheses matter: with an empty strategy set there is no mixed strategy at all, and degenerate games can have infinitely many equilibria: when all payoffs are zero, every pair of mixed strategies is one (and that game is degenerate as soon as a player has two pure strategies).

## Background

- [Nash's theorem](../nash-s-theorem/exists-is-mixed-nash.md): existence of an equilibrium in every finite game, proved from Brouwer's theorem.
- [Every END-OF-THE-LINE instance has a sink](../../../TheoryOfComputation/completeness-other-classes/ppad-and-the-end-of-the-line-problem/exists-sink.md): the parity principle that the Lemke–Howson path instantiates.

## Sources

- B. von Stengel, "Equilibrium computation for two-player games in strategic and extensive form", *Algorithmic Game Theory* (Cambridge University Press 2007), Corollary 3.7, proved by the Lemke–Howson path-following argument (Algorithm 3.6; C. E. Lemke and J. T. Howson, J. SIAM 12 (1964), 413–423).
