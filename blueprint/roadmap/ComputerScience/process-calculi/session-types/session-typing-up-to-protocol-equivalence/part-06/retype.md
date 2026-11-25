# Equivalent contexts preserve the guard condition

Let $\Delta$, $\Xi$ be ownership contexts with $\Delta \approx \Xi$ (equal domains, and at each
endpoint capabilities with equal ranks and tree-equivalent protocols), $e$ an endpoint and $k$ a
natural number. If $\mathrm{Min}_\Delta(e,k)$ holds (every endpoint $d \ne e$ with an active
capability in $\Delta$ has rank $> k$), then $\mathrm{Min}_\Xi(e,k)$ holds.
