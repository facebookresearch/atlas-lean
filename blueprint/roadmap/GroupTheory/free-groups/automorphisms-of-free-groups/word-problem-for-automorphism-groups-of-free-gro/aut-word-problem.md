# The word problem of Aut(Fₙ) for a family of automorphisms

Let $F_n$ be the free group on
$n$ generators and let $g_0, \dots, g_{k-1}$ be automorphisms of $F_n$. A word is a finite list of
letters $(i, b)$ with $i \in \mathbb{N}$ and $b$ a boolean. The word problem for $(g_i)$ is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of lists of pairs of a natural number and a boolean, to a word $w$ such that
every letter $(i, b)$ of $w$ has $i < k$ and the automorphism spelled by $w$ over $(g_i)$ is the
identity; here the letter $(i, \mathrm{true})$ stands for $g_i$ and $(i, \mathrm{false})$ for
$g_i^{-1}$. Bitstrings that do not decode to a word are rejected.
