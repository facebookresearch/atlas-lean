# Approximate two-player Nash equilibria require quasi-polynomial time under the exponential time hypothesis for PPAD

For every constant $\varepsilon > 0$, an $\varepsilon$-approximate Nash equilibrium of an $n \times n$ bimatrix game with payoffs in $[0, 1]$ can be computed in time $n^{O(\log n / \varepsilon^2)}$, because some $\varepsilon$-approximate equilibrium has both strategies uniform over multisets of $O(\log n / \varepsilon^2)$ pure strategies. Conversely, there is a constant $\varepsilon_0 > 0$ such that, assuming the exponential time hypothesis for End-of-Line (solving it requires $2^{\Omega(k)}$ time on circuits with $k$ inputs), computing an $\varepsilon_0$-approximate Nash equilibrium of a bimatrix game requires time $n^{\log^{1 - o(1)} n}$.

## Proof sketch

The upper bound samples $O(\log n/\varepsilon^2)$ pure strategies from each player's equilibrium strategy; Hoeffding's inequality and a union bound over the $2n$ pure strategies show the empirical mixture is an $\varepsilon$-approximate equilibrium, and exhaustive search over such supports finds one. The lower bound reduces End-of-Line, via a constant-gap PCP-like amplification of a Brouwer function with error-correcting encodings, to $\varepsilon_0$-approximate equilibria of games of size $n = 2^{\tilde O(\sqrt k)}$, so that an $n^{o(\log n / \mathrm{polylog} \log n)}$-time algorithm would solve End-of-Line in time $2^{o(k)}$.

## Depends on

- [Mixed Nash equilibrium](../is-mixed-nash.md)
- [Nash equilibrium of a bimatrix game](../../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)

## Proof depends on

- [Computing a Nash equilibrium of a two-player game is PPAD-complete](two-player-nash-ppad-complete.md)

## Sources

- R. J. Lipton, E. Markakis, A. Mehta, "Playing large games using simple strategies", EC 2003.
- A. Rubinstein, "Settling the Complexity of Computing Approximate Two-Player Nash Equilibria", FOCS 2016; SIGecom Exchanges 15(2) (2017), arXiv:1606.04550.
