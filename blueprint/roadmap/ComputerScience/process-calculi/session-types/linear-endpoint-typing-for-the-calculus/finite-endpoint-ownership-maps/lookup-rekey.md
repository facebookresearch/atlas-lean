# Lookups in a rekeyed ownership map

Let $f$ be a map from endpoints to endpoints that is injective on the domain of an ownership context
$\Delta$, $e$ an endpoint and $c$ a capability. Then $f_*\Delta$ maps $e$ to $c$ if and only if
there is an endpoint $d$ with $\Delta(d) = c$ and $f(d) = e$; here $f_*\Delta$ maps $f(d)$ to
$\Delta(d)$ for every $d$ in the domain of $\Delta$.
