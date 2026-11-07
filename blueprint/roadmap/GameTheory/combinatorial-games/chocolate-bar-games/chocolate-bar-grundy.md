# Grundy number of a chocolate bar

Let $f_1, \dots, f_s : \mathbb{N} \to \mathbb{N}$. For
coordinates $x = (x_1, \dots, x_s) \in \mathbb{N}^s$ and a width $z \in \mathbb{N}$, the position
$(x, z)$ stands for the chocolate bar $\mathrm{CB}(f_1, \dots, f_s, x_1, \dots, x_s, z)$, whose
column at width $w \le z$ extends $\min(f_t(w), x_t) + 1$ cells along axis $t$. A move either
lowers one coordinate $x_i$ to some $u < x_i$, keeping the width $z$, or cuts the width to some
$w < z$, which replaces every $x_t$ by $\min(x_t, f_t(w))$. The Grundy number of $(x, z)$ is the
mex (least natural number not attained) of the Grundy numbers of the positions reachable from
$(x, z)$ in one move. It is defined for all $(x, z)$; the bars themselves are the positions with
$x_t \le f_t(z)$ for all $t$.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Definitions 2, 8, 9 and 10 (two functions) and Section 4, before Theorem 5 (four functions).
