# Capability whose head is a send with a given continuation

A capability $c = (k,S)$ sends with continuation $S'$ when $\mathrm{unf}(S) = {!\mathrm{N}}.S'$, or
$\mathrm{unf}(S) = {!(r,j,T)}.S'$ for some polarity $r$, rank $j$ and protocol $T$.
