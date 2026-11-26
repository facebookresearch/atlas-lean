# Type soundness

Let $\delta$ agree with the signature $K$. If a well-formed expression
$e$ has type $\tau$ in the initial context, then every expression $e'$ that $e$ reduces to in
finitely many steps is a value or reduces: a typed program does not go wrong.
