# Head communication preserves endpoint typing

Let $n$ be a natural number, $\Delta$ a compatible ownership context, $a$, $b$ names and $p$, $q$
processes with $\Delta \vdash_n \overline{a}\langle b\rangle.p \mid a(\cdot).q$. Then there are an
endpoint $e$ with name $a$, a capability $c$ of rank $k$ with $\Delta(e) = c$ and a protocol $S'$
with $\Delta[e \mapsto (k,S')][\bar e \mapsto (k,\overline{S'})] \vdash_n p \mid q\{b\}$.
