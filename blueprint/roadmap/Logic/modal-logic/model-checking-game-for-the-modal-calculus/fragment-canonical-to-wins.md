# The fragment game's winning region is contained in Wins

Let $M$ be a Kripke model,
$\rho$ an environment, $\varphi$ a fixpoint-free formula and $w$ a world. If the embedded
position $(\varphi, w)$ lies in the winning region of the even player in the fragment game of
$M$ and $\rho$, then the backward-induction winning condition $\mathrm{Wins}_M(\varphi, w)$
holds.

The proof is by induction on $\varphi$, using that the winning region is closed under the
opponent's moves and under the moves of a winning strategy, so no strategy composition is
needed.
