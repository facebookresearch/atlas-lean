# Programs accepted by Algorithm W do not go wrong

Let equality of base types be
decidable, let $K$ be a signature, with finitely many constants, and let $\delta$ agree with it.
If Algorithm W, run on the initial context and a well-formed expression $e$ with any counter
$n$, returns a substitution $s$, a monotype $\tau$ and a counter $n'$, then every expression that
$e$ reduces to in finitely many steps is a value or reduces.
