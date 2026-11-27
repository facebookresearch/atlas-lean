# Erasing a role with an absent name preserves typing

Let $n$ be a natural number, $\Delta$ an ownership context, $p$ a process and $z$ an endpoint whose
name does not occur in $p$ (in no subject or payload position, the tracked index being raised under
each binder). If $\Delta \vdash^{\simeq}_n p$, then $\Delta \setminus z \vdash^{\simeq}_n p$.
