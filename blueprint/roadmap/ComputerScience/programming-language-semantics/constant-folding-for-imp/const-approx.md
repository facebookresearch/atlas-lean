# A constant table approximates an IMP state

Let $t : \mathbb{N} \to \mathbb{N} \cup \{\bot\}$ be a constant table and $s : \mathbb{N} \to \mathbb{N}$ an IMP state. The table $t$ approximates $s$ when every recorded entry agrees with $s$: for all variable indices $x$ and naturals $n$, if $t(x) = n$ then $s(x) = n$. Entries $t(x) = \bot$ impose nothing.
