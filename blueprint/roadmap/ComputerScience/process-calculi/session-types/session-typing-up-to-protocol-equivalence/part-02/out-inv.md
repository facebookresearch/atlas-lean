# Output inversion for conversion typing

Let $n$ be a natural number, $\Delta$ an ownership context, $a$, $b$ names and $p$ a process with
$\Delta \vdash^{\simeq}_n \overline{a}\langle b\rangle.p$. Then there are an endpoint $e$ with name
$a$ and a capability $c = (k,S)$ with $\Delta(e) = c$ such that either $\mathrm{unf}(S) =
{!\mathrm{N}}.S'$ for some protocol $S'$, or there are an endpoint $d$ with name $b$ and polarity
$r$, a capability $v$ with $\Delta(d) = v$, a rank $j$ and protocols $T$, $S'$ with $\mathrm{unf}(S)
= {!(r,j,T)}.S'$ and $v \approx (j,T)$.
