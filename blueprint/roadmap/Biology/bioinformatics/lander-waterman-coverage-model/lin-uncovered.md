# Exact uncovered probability of a base of a linear genome

On a linear genome with bases $\{0, \dots, G-1\}$, let $N$ reads of length $L \le G$ have start
positions $s_1, \dots, s_N \in \{0, \dots, G - L\}$, the read starting at $s$ covering the base
$x$ when $s \le x < s + L$. For every base $x$, the [normalized count](normalized-count.md) over
these start tuples (each set counted relative to $(G - L + 1)^N$ tuples) of the tuples in which
no read covers $x$ is

$$\Bigl(1 - \frac{k}{G - L + 1}\Bigr)^N, \qquad k = \min(x, G - L) + 1 - (x + 1 - L),$$

where $k$ is the [number of starts covering $x$](card-lin-covering-starts.md) and $x + 1 - L$ is
natural subtraction. When the $N$ start positions are independent and uniform on
$\{0, \dots, G - L\}$, this is the probability that $x$ is uncovered.
