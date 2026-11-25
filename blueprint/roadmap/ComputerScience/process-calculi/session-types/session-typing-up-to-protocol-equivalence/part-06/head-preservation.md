# Head preservation for a conversion-ranked opposite pair

Let $n$ be a natural number, $\Delta$ a semantically compatible ownership context, $a$, $b$ names
and $p$, $q$ processes with $\Delta \vdash^{\mathrm{rk}\simeq}_n \overline{a}\langle b\rangle.p \mid
a(\cdot).q$. Then there are an endpoint $e$ with name $a$, capabilities $c = (k,S)$, $d = (k,U)$ and
protocols $S'$, $U'$ with $\Delta(e) = c$, $\Delta(\bar e) = d$ and $U' \simeq \overline{S'}$, such
that either $\mathrm{unf}(S) = {!\mathrm{N}}.S'$ and $\mathrm{unf}(U) = {?\mathrm{N}}.U'$, or there
are an endpoint $f$ with name $b$ and polarity $r$, a capability $v$, a rank $j$ and protocols $T$,
$T'$ with $\Delta(f) = v \approx (j,T)$, $\mathrm{unf}(S) = {!(r,j,T)}.S'$, $\mathrm{unf}(U) =
{?(r,j,T')}.U'$ and $T' \simeq T$; in both cases $\Delta[e \mapsto (k,S')][\bar e \mapsto (k,U')]
\vdash^{\mathrm{rk}\simeq}_n p \mid q\{b\}$.
