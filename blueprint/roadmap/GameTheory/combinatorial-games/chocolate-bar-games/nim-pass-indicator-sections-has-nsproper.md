# Sections of the Nim pass indicator with the NS property

Let $s \in \mathbb{N}$ and
$m \in \mathbb{N}^s$ with $m_i > 0$ for every $i < s$, and let $F : \mathbb{N}^s \to \mathbb{N}$ be
the pass indicator of $m$: $F(x) = 1$ if $m_j \le x_j$ for some $j$, and $F(x) = 0$ otherwise.
For $x \in \mathbb{N}^s$, $i < s$ and $t \in \mathbb{N}$ write $x[i \mapsto t]$ for $x$ with its
$i$-th coordinate replaced by $t$. Then the following are equivalent: (a) for all
$x \in \mathbb{N}^s$ and $i < s$, the function $t \mapsto F(x[i \mapsto t])$ has the NS property;
(b) $m_i$ is even for every $i < s$.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Lemma 10 (`integers-2025-G3-lem-10`).
