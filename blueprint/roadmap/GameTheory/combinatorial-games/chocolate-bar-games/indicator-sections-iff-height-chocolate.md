# Height-one chocolate bars with nim-sum Grundy numbers

Let $s \in \mathbb{N}$ and let
$F : \mathbb{N}^s \to \mathbb{N}$ be monotone for the coordinatewise order, with $F(x) \le 1$ for
all $x$. For $x \in \mathbb{N}^s$, $i < s$ and $t \in \mathbb{N}$ write $x[i \mapsto t]$ for $x$
with its $i$-th coordinate replaced by $t$, and suppose that for all $x$ and $i$ there is a $t$
with $F(x[i \mapsto t]) = 1$. Write $\oplus$ for nim-sum. Then the following are equivalent:
(a) for all $x \in \mathbb{N}^s$ and $i < s$ there is an even $m \in \mathbb{N}$ (depending on $x$
and $i$) such that $F(x[i \mapsto t]) = 1$ for $t \ge m$ and $F(x[i \mapsto t]) = 0$ for $t < m$;
(b) for all $x \in \mathbb{N}^s$ and $y \in \mathbb{N}$ with $y \le F(x)$, the Grundy number of the
chocolate bar $\mathrm{CB}(F, x_0, \dots, x_{s-1}, y)$ is
$x_0 \oplus \cdots \oplus x_{s-1} \oplus y$.

The hypothesis that every section takes the value $1$ is that of Lemma 9, from which the
corollary is derived.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Corollary 1.
