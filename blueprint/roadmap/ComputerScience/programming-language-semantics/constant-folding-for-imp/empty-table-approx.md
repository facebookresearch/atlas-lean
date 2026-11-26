# The empty constant table approximates every IMP state

A constant table is a function $t : \mathbb{N} \to \mathbb{N} \cup \{\bot\}$ (an option of a natural number) recording, for some variable indices $x$, a known value $t(x) = n$; $t(x) = \bot$ means no known value. A table $t$ approximates an IMP state $s$ when $s(x) = n$ whenever $t(x) = n$. The empty table, with $t(x) = \bot$ for every $x$, approximates every IMP state $s$.
