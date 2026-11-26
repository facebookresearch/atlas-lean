# Matching send and receive heads of two capabilities

Let $c = (k,S)$ and $d = (k',U)$ be capabilities and $S'$, $U'$ protocols. The capabilities have
matching communication heads with continuations $S'$ and $U'$ in exactly two cases: $\mathrm{unf}(S)
= {!\mathrm{N}}.S'$ and $\mathrm{unf}(U) = {?\mathrm{N}}.U'$; or there are a polarity $r$, a rank
$j$ and protocols $T$, $V$ with $\mathrm{unf}(S) = {!(r,j,T)}.S'$, $\mathrm{unf}(U) = {?(r,j,V)}.U'$
and $V \simeq T$ (tree-equivalent payloads).
