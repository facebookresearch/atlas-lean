# Uncommon equations over a finite abelian group

Let $G$ be a finite abelian group,
let $a_1, \dots, a_k$ be integers, let $r$ be a natural number, and let $S \subseteq G^k$ be
the set of solutions of $a_1x_1 + \cdots + a_kx_k = 0$. The equation is $r$-uncommon over
$G$ when there are functions $w_1, \dots, w_r \colon G \to \mathbb{R}$ with $w_c(x) \ge 0$ for
all $c$ and $x$, and $w_1(x) + \cdots + w_r(x) = 1$ for every $x \in G$, such that

$$r^{k-1} \sum_{c=1}^{r} \sum_{(x_1, \dots, x_k) \in S} \prod_{i=1}^{k} w_c(x_i) < |S|,$$

where $r^{k-1}$ is read as $1$ when $k = 0$.

The functions $w_c$ form a fractional $r$-colouring of $G$, and the double sum is its
weighted count of monochromatic solutions. For $k \ge 1$ the condition says that this count
is below $r^{1-k}|S|$, its value for the uniform weights $w_c(x) = 1/r$.

## Sources

- Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least Three Colors*, INTEGERS 25 (2025), Article A88, Sections 1-2 (equation (2.1)).
