# Send heads are active for both payload sorts

Let $c$ be a capability with protocol $S$ and let $S'$ be a protocol. If $c$ sends with continuation
$S'$, that is $\mathrm{unf}(S) = {!\mathrm{N}}.S'$ or $\mathrm{unf}(S) = {!(r,j,T)}.S'$ for some
polarity $r$, rank $j$ and protocol $T$, then $\mathrm{unf}(S) \ne \mathrm{end}$.
