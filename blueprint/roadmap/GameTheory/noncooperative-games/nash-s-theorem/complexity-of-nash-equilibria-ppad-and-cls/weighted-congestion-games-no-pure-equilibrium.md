# Weighted congestion games with nonlinear delays may lack pure equilibria

In a weighted congestion game, player $i$ has weight $w_i > 0$ and the delay of resource $e$ depends on the total weight of players using it. There exist weighted congestion games with two players and polynomial (in particular quadratic) delay functions that have no pure Nash equilibrium; in contrast, weighted congestion games with affine or exponential delay functions always possess pure Nash equilibria. Deciding whether a weighted network congestion game has a pure Nash equilibrium is NP-hard.

## Proof sketch

An explicit four-resource network with two players of weights $1$ and $2$ and quadratic delays has a best-response cycle through all four strategy profiles, so no profile is stable. For affine delays a weighted potential quadratic in the resource loads exists, and for exponential delays a potential of exponential form exists. NP-hardness embeds a satisfiability instance into copies of the cycling gadget that are stabilized exactly by satisfying assignments.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)

## Proof depends on

- [Rosenthal's theorem](../../potential-games/is-exact-potential-potential.md)

## Sources

- M. Goemans, V. Mirrokni, A. Vetta, "Sink Equilibria and Convergence", FOCS 2005.
- J. Dunkel, A. S. Schulz, "On the complexity of pure-strategy Nash equilibria in congestion and local-effect games", Mathematics of Operations Research 33(4) (2008).
- T. Harks, M. Klimm, "On the existence of pure Nash equilibria in weighted congestion games", Mathematics of Operations Research 37(3) (2012).
