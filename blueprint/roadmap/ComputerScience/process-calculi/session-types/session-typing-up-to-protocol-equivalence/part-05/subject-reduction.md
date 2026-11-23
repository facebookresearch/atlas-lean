# Subject reduction at a compatible conversion interface

Let $n$ be a natural number, $\Delta$ a semantically compatible ownership context (whenever
$\Delta(e) = c$ and $\Delta(\bar e) = d$, then $d \approx \bar c$) and $p$, $q$ processes with
$\Delta \vdash^{\simeq}_n p$ and $p \to q$. Then there is a semantically compatible ownership
context $\Xi$ with $\Xi \vdash^{\simeq}_n q$ such that $\Xi = \Delta$ or $\Xi$ is a semantic advance
of $\Delta$: $\Xi = \Delta[e \mapsto (k,S')][\bar e \mapsto (k',U')]$ for an endpoint $e$ with
$\Delta(e) = (k,S)$ and $\Delta(\bar e) = (k',U) \approx (k,\overline{S})$, where the heads of $S$
and $U$ are a matching send and receive (of a name, or of an endpoint with the same polarity and
rank and tree-equivalent payloads) with continuations $S'$ and $U'$, and $U' \simeq \overline{S'}$.
