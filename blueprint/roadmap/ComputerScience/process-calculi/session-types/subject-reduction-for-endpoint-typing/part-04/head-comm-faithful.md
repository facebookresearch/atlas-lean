# Head communication preserves typing and records the matched output

Let $n$ be a natural number, $\Delta$ a compatible ownership context (whenever it maps an endpoint
to $c$ and its opposite to $d$, then $d = \bar c$), $a$, $b$ names and $p$, $q$ processes with
$\Delta \vdash_n \overline{a}\langle b\rangle.p \mid a(\cdot).q$ (endpoint typing). Then there are
an endpoint $e$ with name $a$, a capability $c = (k,S)$ and a protocol $S'$ with $\Delta(e) = c$,
$\Delta(\bar e) = \bar c$, the output of $b$ on $e$ matched with continuation $S'$ (a passive send
${!\mathrm{N}}.S'$, or an endpoint send ${!(r,j,T)}.S'$ of an owned endpoint $d \ne e, \bar e$ with
name $b$, polarity $r$ and $\Delta(d) = (j,T)$), and $\Delta[e \mapsto (k,S')][\bar e \mapsto
(k,\overline{S'})] \vdash_n p \mid q\{b\}$.
