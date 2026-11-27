# Dual-continuation update preserves compatibility

Let $\Delta$ be a compatible ownership context (whenever it maps an endpoint to $c$ and its opposite
to $d$, then $d = \bar c$), $e$ an endpoint, $c$ a capability of rank $k$ and $S$ a protocol. Then
$\Delta[e \mapsto (k,S)][\bar e \mapsto (k,\overline{S})]$ is compatible.
