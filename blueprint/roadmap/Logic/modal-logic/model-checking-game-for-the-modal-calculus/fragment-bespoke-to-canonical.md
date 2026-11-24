# Winning Verifier strategies transfer to the fragment game

Let $M$ be a Kripke model,
$\rho$ an environment, $\sigma$ a Verifier strategy of the model-checking game on $M$,
$\varphi$ a fixpoint-free formula and $w$ a world. If $\sigma$ wins in environment $\rho$ from
the game position with formula $\varphi$, world $w$ and empty binder stack, then the positional
strategy of the even player induced by $\sigma$ wins from the embedded position $(\varphi, w)$
in the fragment game of $M$ and $\rho$.

Every play conforming to the induced strategy reaches the absorbing winning state: it cannot
reach the losing state, by the finite-play clause for $\sigma$ applied to the segment before the
first losing state, and it cannot stay among embedded positions forever, since fragment moves
strictly decrease the formula.
