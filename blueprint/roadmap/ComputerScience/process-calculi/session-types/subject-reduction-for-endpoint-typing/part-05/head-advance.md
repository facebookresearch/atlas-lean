# Typed head communication yields a semantic advancement

Let $n$ be a natural number, $\Delta$ a semantically compatible ownership context, $a$, $b$ names
and $p$, $q$ processes. If $\Delta \vdash^{\simeq}_n \overline{a}\langle b\rangle.p \mid a(\cdot).q$
(conversion typing), then there is a semantically compatible ownership context $\Xi$ with $\Xi
\vdash^{\simeq}_n p \mid q\{b\}$ such that $\Delta$ advances semantically to $\Xi$.
