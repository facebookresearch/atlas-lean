# Lexicographic order on edge keys

For pairs of natural numbers $(w, i)$ and $(w', i')$,
$(w, i) \preceq (w', i')$ holds when $w < w'$, or $w = w'$ and $i \le i'$. This is the
non-strict lexicographic order on $\mathbb{N} \times \mathbb{N}$; Kruskal's algorithm applies it to
keys (weight, input ordinal).
