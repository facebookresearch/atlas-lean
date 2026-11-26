# Endpoint typing drops a role whose name does not occur

Let $n$ be a natural number, $\Delta$ an ownership context, $p$ a process and $z$ an endpoint whose
name does not occur in $p$ (in no subject or payload position, the tracked index being raised under
each binder). If $\Delta \vdash_n p$, then $\Delta \setminus z \vdash_n p$.
