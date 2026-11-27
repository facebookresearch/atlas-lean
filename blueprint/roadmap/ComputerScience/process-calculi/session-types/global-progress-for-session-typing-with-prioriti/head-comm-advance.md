# Ranked head communication yields a dual advance

Let $n$ be a natural number, $\Delta$ a compatible ownership context, $a$, $b$ names and $p$, $q$
processes. If $\Delta \vdash^{\mathrm{rk}}_n \overline{a}\langle b\rangle.p \mid a(\cdot).q$, then
there is a compatible ownership context $\Xi$ with $\Xi \vdash^{\mathrm{rk}}_n p \mid q\{b\}$ that
is a dual advance of $\Delta$: for some endpoint $e$ and capability $c = (k,S)$ with $\Delta(e) = c$
and $\Delta(\bar e) = \bar c$, and some protocol $S'$ with $\mathrm{unf}(S) = {!\mathrm{N}}.S'$ or
$\mathrm{unf}(S) = {!(r,j,T)}.S'$, we have $\Xi = \Delta[e \mapsto (k,S')][\bar e \mapsto
(k,\overline{S'})]$. (Compatible: opposite endpoints present in the context carry dual
capabilities.)
