# Exists weyl Of Swap Label mul eq right Hurwitz

Atomic Weyl lift of one directed right-Hurwitz step.

Purpose: transport a single forward move `[a, b] ↦ [b, conjLabel b a]` from
permutations to stable Steinberg Weyl words with an exact exhibited
coefficient. Orientation is head-left: `Wₐ(u) * W_b(v) = W_b(v) * W_conj(q)`.
Hypotheses: ordered endpoint labels `a b`, units `u v`, `[Ring R]` only; no
commutativity, field, or finiteness hypothesis beyond the labels. The witness
`q` is the exhaustive endpoint-incidence table: disjoint gives `u`;
`a.1 = b.2` gives `(-v) * u`; `a.1 = b.1` gives `v⁻¹ * u`; `a.2 = b.1` gives
`u * v`; `a.2 = b.2` gives `u * (-v⁻¹)`; `a = b` gives `-(v⁻¹ * u * v⁻¹)`;
`a` reversed from `b` gives `-(v * u * v)`. Nonclaims: no `ReflTransGen`
trace recursion, no terminal-pair deletion, no torus/cocycle landing, no
strict descent, no kernel generation, no TWT, and no Matsumoto theorem.
