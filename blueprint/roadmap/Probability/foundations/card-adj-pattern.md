# Prescribed adjacency patterns

Let $n, k \in \mathbb{N}$, let $V = \{0, \dots, n-1\}$, fix a vertex $v \in V$, distinct target vertices $e_1, \dots, e_k \in V$ (an injective map $i \mapsto e_i$; a target may equal $v$), and a pattern $p_1, \dots, p_k \in \{\mathrm{true}, \mathrm{false}\}$. The number of adjacency functions $a \colon V \times V \to \{\mathrm{true}, \mathrm{false}\}$ with $a(v, e_i) = p_i$ for every $i$ is

$$2^{\,n^2 - k}.$$

The $k$ prescribed entries are forced and the other $n^2 - k$ entries are free.
