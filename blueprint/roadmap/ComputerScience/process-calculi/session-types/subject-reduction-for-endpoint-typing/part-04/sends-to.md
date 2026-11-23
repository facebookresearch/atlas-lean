# A matched output head is a send with the same continuation

Let $\Delta$ be an ownership context, $e$ an endpoint, $c = (k,S)$ a capability, $S'$ a protocol and
$b$ a name. If the output of $b$ on $e$ is matched with continuation $S'$ (either $\mathrm{unf}(S) =
{!\mathrm{N}}.S'$, or $\mathrm{unf}(S) = {!(r,j,T)}.S'$ for an owned endpoint $d$ with name $b$,
polarity $r$ and $\Delta(d) = (j,T)$, $d \ne e$, $d \ne \bar e$), then $c$ sends with continuation
$S'$: $\mathrm{unf}(S)$ is ${!\mathrm{N}}.S'$ or ${!(r,j,T)}.S'$ for some $r$, $j$, $T$.
