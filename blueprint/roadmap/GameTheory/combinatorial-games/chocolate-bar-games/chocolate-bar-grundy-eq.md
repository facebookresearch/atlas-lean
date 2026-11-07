# Mex recursion for the Grundy number of a chocolate bar

Let $f_1, \dots, f_s$ be
functions $\mathbb{N} \to \mathbb{N}$ and write $G(x, z)$ for the Grundy number of the chocolate
bar with coordinates $x = (x_1, \dots, x_s) \in \mathbb{N}^s$ and width $z \in \mathbb{N}$. For
all $x$ and $z$, $G(x, z)$ is the least natural number $m$ such that $m \ne G(x', z)$ for every
$x'$ obtained from $x$ by replacing one coordinate $x_i$ with some $u < x_i$, and
$m \ne G(x^{(w)}, w)$ for every $w < z$, where $x^{(w)}_t = \min(x_t, f_t(w))$ for all $t$.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Definitions 9 and 10.
