# An active same-rank peer violates the guard condition

Let $\Delta$ be an ownership context, $e$ an endpoint with opposite endpoint $\bar e$ (same name,
other polarity) and $c$ a capability. If $\Delta(\bar e) = c$ and the protocol of $c$ does not have
head $\mathrm{end}$, then $\mathrm{Min}_\Delta(e, k)$ fails for $k$ the rank of $c$, where
$\mathrm{Min}_\Delta(e,k)$ requires every endpoint $d \ne e$ with an active capability in $\Delta$
to have rank $> k$.
