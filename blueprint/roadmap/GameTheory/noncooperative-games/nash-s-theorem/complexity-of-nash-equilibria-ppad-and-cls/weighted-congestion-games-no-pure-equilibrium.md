# Weighted congestion games with nonlinear delays may lack pure equilibria

In a weighted congestion game, player $i$ has weight $w_i > 0$ and the delay of resource $e$ depends on the total weight of players using it. There exist two-player single-commodity weighted network congestion games with polynomial delay functions of degree at most $2$ with nonnegative coefficients that have no pure Nash equilibrium; in contrast, weighted congestion games whose delays are all affine, or all of the form $a_e e^{\varphi x} + b_e$ with one common $\varphi$, always possess pure Nash equilibria, and for games with at least three players these two classes are the only (twice continuously differentiable) classes of delay functions that guarantee pure equilibria. Deciding whether a weighted network congestion game has a pure Nash equilibrium is strongly NP-hard.

## Proof sketch

In the explicit two-player network every player has two relevant paths and the four strategy profiles form a best-response cycle, so no profile is stable. For affine delays a weighted potential quadratic in the resource loads exists, and for exponential delays with a common rate a potential of exponential form exists; conversely, for any other class of delays an instance without pure equilibrium can be built. NP-hardness combines copies of a gadget without pure equilibrium so that a pure equilibrium exists exactly for yes-instances of the source problem.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)

## Proof depends on

- [Rosenthal's theorem](../../potential-games/is-exact-potential-potential.md)
- [Weighted congestion games with affine latencies are weighted potential games](../../atomic-congestion-games-with-affine-delays/atomic-congestion-efficiency/weighted-congestion-games-with-affine-latencies-are-weighted-potential-games.md)

## Sources

- M. Goemans, V. Mirrokni, A. Vetta, "Sink Equilibria and Convergence", FOCS 2005.
- J. Dunkel, A. S. Schulz, "On the complexity of pure-strategy Nash equilibria in congestion and local-effect games", Mathematics of Operations Research 33(4) (2008).
- T. Harks, M. Klimm, "On the existence of pure Nash equilibria in weighted congestion games", Mathematics of Operations Research 37(3) (2012); ICALP 2010.
