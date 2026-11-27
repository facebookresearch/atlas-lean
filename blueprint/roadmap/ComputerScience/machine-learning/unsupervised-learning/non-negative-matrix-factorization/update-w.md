# Lee–Seung multiplicative update of W

The Lee–Seung multiplicative update of $W$ (Lee and Seung 2001, Theorem 1): for finite index sets
$n, k$, $X \in \mathbb{R}^{m \times n}$, $W \in \mathbb{R}^{m \times k}$ and
$H \in \mathbb{R}^{k \times n}$, the updated matrix has entries

$$W'_{ia} = W_{ia} \, \frac{(X H^\top)_{ia}}{(W H H^\top)_{ia}},$$

where an entry with a zero denominator becomes $0$.
