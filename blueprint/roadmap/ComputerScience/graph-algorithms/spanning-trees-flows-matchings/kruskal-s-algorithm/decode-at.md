# Decoding a raw edge at an ordinal

Given natural numbers $n$ and $i$ and a raw edge
with source $s$, target $t$ and weight $w$, decoding at ordinal $i$ returns the validated
edge on the vertices $\{0, \dots, n-1\}$ with ordinal $i$, source $s$, target $t$ and
weight $w$ when $s < n$ and $t < n$, and returns no edge otherwise.
