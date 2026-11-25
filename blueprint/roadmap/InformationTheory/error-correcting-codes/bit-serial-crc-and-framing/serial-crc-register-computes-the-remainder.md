# A bit-serial CRC register computes the remainder

Let $g = X^r + g_{r-1}X^{r-1} + \dots + g_0$ be a monic polynomial over $\mathbb F_2$ of degree $r \ge 1$. The
zero-initialized, unreflected bit-serial CRC register holds a state $S$, a polynomial over $\mathbb F_2$ of degree less than
$r$ (its $r$ coefficients are the register cells), starts from $S = 0$, and on each input bit $b \in \{0, 1\}$ moves to

$$S \mapsto (X S + b) \bmod g ,$$

that is, it shifts the cells up by one place, enters $b$ at the bottom, and adds $g_0, \dots, g_{r-1}$ when the bit shifted
out of the top cell is $1$. Then after the bits $b_0, b_1, \dots, b_{n-1}$ have been read, most significant first, the state is

$$S = \Big(\sum_{j=0}^{n-1} b_j X^{n-1-j}\Big) \bmod g .$$

In particular, for a payload $b_0, \dots, b_{l-1}$ with message polynomial $m = \sum_{j<l} b_j X^{l-1-j}$, reading the payload
followed by $r$ zero bits leaves $S = (X^r m) \bmod g$, so the [CRC encoding](../cyclic-redundancy-checks/encode.md) of $m$ is
$X^r m + S$: the payload bits followed by the $r$ coefficients of $S$, most significant first. Leading zero bits of the payload
do not change $m$, and the frame keeps its declared length $l + r$.

The formula follows by induction on $n$, since $X(u \bmod g) + b \equiv X u + b \pmod g$ and the left side has degree at most $r$.

## Depends on

- [CRC encoder](../cyclic-redundancy-checks/encode.md)

## Sources

- W. W. Peterson and D. T. Brown, "Cyclic codes for error detection", *Proceedings of the IRE* 49(1):228–235, 1961.
- S. Lin and D. J. Costello, *Error Control Coding*, 2nd edition, Pearson Prentice Hall, 2004, Chapter 5 (cyclic codes and their shift-register encoders).
