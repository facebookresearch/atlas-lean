# Ranked head communication exposes peers and residual typing

Let $n$ be a natural number, $\Delta$ a compatible ownership context (whenever it maps an endpoint
to $c$ and the opposite endpoint to $d$, then $d = \bar c$), $a$, $b$ names and $p$, $q$ processes
with $\Delta \vdash^{\mathrm{rk}}_n \overline{a}\langle b\rangle.p \mid a(\cdot).q$. Then there are
an endpoint $e$ with name $a$, a capability $c = (k,S)$ and a protocol $S'$ such that $\Delta(e) =
c$, $\Delta(\bar e) = \bar c$, the output is matched, and $\Delta[e \mapsto (k,S')][\bar e \mapsto
(k,\overline{S'})] \vdash^{\mathrm{rk}}_n p \mid q\{b\}$. The output is matched when either
$\mathrm{unf}(S) = {!\mathrm{N}}.S'$, or there are an endpoint $d$ with name $b$ and polarity $r$, a
rank $j$ and a protocol $T$ with $\mathrm{unf}(S) = {!(r,j,T)}.S'$, $\Delta(d) = (j,T)$, $d \ne e$
and $d \ne \bar e$.
