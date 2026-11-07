# Nim with a restricted pass

Let $s \in \mathbb{N}$ and $m \in \mathbb{N}^s$ with $m_i > 0$
for every $i < s$, and let $F : \mathbb{N}^s \to \mathbb{N}$ be the pass indicator of $m$:
$F(x) = 1$ if $m_j \le x_j$ for some $j$, and $F(x) = 0$ otherwise. Write $\oplus$ for nim-sum.
Then the following are equivalent: (a) for all $x \in \mathbb{N}^s$ and $p \in \mathbb{N}$ with
$p \le F(x)$, the Grundy number of the chocolate bar $\mathrm{CB}(F, x_0, \dots, x_{s-1}, p)$ is
$x_0 \oplus \cdots \oplus x_{s-1} \oplus p$; (b) $m_i$ is even for every $i < s$.

The bar is Nim on $s$ piles with a one-time pass usable only while $F(x) = 1$: removing stones
from a pile, reaching $x'$, replaces $p$ by $\min(F(x'), p)$, and the pass lowers $p$ from $1$
to $0$.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Corollary 2 (`integers-2025-G3-cor-2`).
