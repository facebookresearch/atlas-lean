# Merkle–Damgård hash with length strengthening

Let $h : S \times B \to S$ be a compression
function, $iv \in S$ an initial value and $\ell : \mathbb{N} \to B$ a length encoding. The hash of
a list of blocks $M = (x_1, \dots, x_L)$ is $h(z_L, \ell(L))$, where $z_0 = iv$ and
$z_i = h(z_{i-1}, x_i)$ for $1 \le i \le L$.
