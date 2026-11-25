# Matched output head of a capability

Let $\Delta$ be an ownership context, $e$ an endpoint, $c = (k,S)$ a capability, $S'$ a protocol and
$b$ a name. The output of $b$ on $e$ is matched, with continuation $S'$, in exactly two cases:
either $\mathrm{unf}(S) = {!\mathrm{N}}.S'$ (passive payload); or there are an endpoint $d$ with
name $b$ and polarity $r$, a rank $j$ and a protocol $T$ with $\mathrm{unf}(S) = {!(r,j,T)}.S'$,
$\Delta(d) = (j,T)$, $d \ne e$ and $d \ne \bar e$ (delegated endpoint).
