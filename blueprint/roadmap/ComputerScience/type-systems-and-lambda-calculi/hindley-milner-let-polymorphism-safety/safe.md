# Typed programs are safe

Let $\delta$ agree with the signature $K$. If a well-formed
expression $e$ has type $\tau$ in the initial context, then no configuration reachable from $e$
in `opSem hK` is stuck.
