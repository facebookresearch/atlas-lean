# Priority of the outer binder in the regression play

The starting position of the
regression play, consisting of the formula $\mu X.\,\nu Y.\,X$, the unique world and the empty
binder stack, has priority $1$: a $\mu$-binder position with $k$ binders on the stack has
priority $2k + 1$, and here $k = 0$.

Under fixed priorities ($\mu \mapsto 1$, $\nu \mapsto 2$) the greatest priority recurring on this
play would be $2$ (even, Verifier wins); with priorities increasing with nesting depth (the inner
$\nu$ here has priority $4$) and the least-priority rule, the least binder priority recurring on
this play is $1$ (odd, Refuter wins).
