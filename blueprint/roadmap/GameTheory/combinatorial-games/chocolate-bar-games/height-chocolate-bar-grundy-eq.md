# Mex recursion for chocolate bars with a height function

Let $s \in \mathbb{N}$ and
$F : \mathbb{N}^s \to \mathbb{N}$, and write $G(x, y)$ for the Grundy number of the chocolate bar
$\mathrm{CB}(F, x_1, \dots, x_s, y)$. For all $x \in \mathbb{N}^s$ and $y \in \mathbb{N}$,
$G(x, y)$ is the least natural number $m$ such that $m \ne G(x', \min(F(x'), y))$ for every $x'$
obtained from $x$ by lowering one coordinate $x_i$ to some $u < x_i$, and $m \ne G(x, v)$ for
every $v < y$.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Definition 17.
