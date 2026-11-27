# Computing a Nash equilibrium of a two-player game is PPAD-complete

The class PPAD consists of total search problems polynomial-time reducible to End-of-Line: given Boolean circuits $S, P$ on $\{0,1\}^k$ with $P(0^k) = 0^k \ne S(0^k)$, find a vertex $x$ with $P(S(x)) \neq x$ (a sink, possibly $0^k$) or with $x \neq 0^k$ and $S(P(x)) \neq x$ (a source other than $0^k$) of the directed graph with arcs $x \to S(x)$ whenever $P(S(x)) = x$; such a vertex always exists. Computing an $\varepsilon$-approximate Nash equilibrium of a game with three or more players, for $\varepsilon = 2^{-\mathrm{poly}}$, is PPAD-complete (exact equilibria may be irrational, and the exact problem is FIXP-complete), and computing a Nash equilibrium of a two-player (bimatrix) game is PPAD-complete. Moreover, for two-player games it is PPAD-hard to compute an $\varepsilon$-approximate Nash equilibrium for $\varepsilon = 1/\mathrm{poly}(n)$, so no fully polynomial-time approximation scheme exists unless PPAD $\subseteq$ P.

## Proof sketch

For three or more players, Daskalakis, Goldberg and Papadimitriou reduce End-of-Line to finding a Brouwer fixed point of a piecewise-linear function on a three-dimensional cube discretized into exponentially many small cells (via Sperner-type colourings), then simulate the arithmetic of this function by graphical games with gadget players implementing addition, multiplication by constants and comparison; equilibria of the graphical game encode approximate fixed points, at exponentially small precision $\varepsilon = 2^{-\mathrm{poly}}$. Multiplayer graphical games reduce to normal-form games through a generalized matching-pennies construction that forces each player to spread probability over groups of strategies. The inverse-polynomial bound for two players needs a different reduction. Chen, Deng and Teng reduce End-of-Line to a discrete fixed-point problem on a high-dimensional grid of constant side length, so that each coordinate needs only constant resolution and the polynomial dimension carries the information, and encode this problem directly in a bimatrix game. Their precision analysis shows that every $1/\mathrm{poly}(n)$-approximate equilibrium of that game yields a solution, giving PPAD-hardness of inverse-polynomial approximation and hence of exact two-player equilibria.

## Depends on

- [Mixed Nash equilibrium](../is-mixed-nash.md)
- [Nash equilibrium of a bimatrix game](../../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)
- [Search problems: FNP, FP and TFNP](../../../../TheoryOfComputation/complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)
- [END-OF-THE-LINE is total](../../../../TheoryOfComputation/completeness-other-classes/ppad-and-the-end-of-the-line-problem/exists-solution.md)

## Proof depends on

- [Nash's theorem](../exists-is-mixed-nash.md)
- [Two-player Nash equilibrium is in PPAD](../../bimatrix-games-and-the-lemke-howson-algorithm/bimatrix-polyhedral-theory/two-player-nash-equilibrium-is-in-ppad.md)

## Sources

- C. Daskalakis, P. W. Goldberg, C. H. Papadimitriou, "The Complexity of Computing a Nash Equilibrium", SIAM Journal on Computing 39(1) (2009); STOC 2006.
- X. Chen, X. Deng, S.-H. Teng, "Settling the Complexity of Computing Two-Player Nash Equilibria", Journal of the ACM 56(3) (2009); FOCS 2006.
- K. Etessami, M. Yannakakis, "On the Complexity of Nash Equilibria and Other Fixed Points", SIAM Journal on Computing 39(6) (2010); FOCS 2007 (FIXP-completeness of exact equilibria for three or more players).
