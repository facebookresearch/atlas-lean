# Injective rekeying preserves the guard condition

Let $\Delta$ be an ownership context, $f$ a map from endpoints to endpoints that is injective on the
domain of $\Delta$, $e$ an endpoint and $k$ a natural number. Write $f_*\Delta$ for the context that
maps $f(d)$ to $\Delta(d)$ for every $d$ in the domain of $\Delta$. If $\mathrm{Min}_\Delta(e,k)$
holds (every endpoint $d \ne e$ with an active capability in $\Delta$ has rank $> k$), then
$\mathrm{Min}_{f_*\Delta}(f(e),k)$ holds.
