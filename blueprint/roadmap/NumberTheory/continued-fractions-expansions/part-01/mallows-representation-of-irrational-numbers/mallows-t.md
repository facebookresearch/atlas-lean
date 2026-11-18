# The map $T$

Let $x = \langle x_1, x_2, \dots \rangle$ be a sequence over
$\{O_L, E_R, O_R, E_L\}$ and let $o(1) < o(2) < \cdots$ be the positions $j$ with
$x_j \in \{O_L, O_R\}$. The sequence $T(x) = \langle T_1(x), T_2(x), \dots \rangle$ over
$\{L, M, R\}$ is defined as follows. If $o(i + 1) = o(i) + 1$, then $T_i(x)$ is $L$ when
$x_{o(i)} = O_L$ and $R$ otherwise. If $o(i + 1) \ne o(i) + 1$, then $T_i(x)$ is $M$ when
$x_{o(i)} \ne x_{o(i + 1)}$, $L$ when $x_{o(i)} = x_{o(i + 1)} = O_R$, and $R$ when
$x_{o(i)} = x_{o(i + 1)} \ne O_R$.

If there are only finitely many such positions, $o(i)$ is taken to be $1$ for every $i$ larger
than their number.

## Sources

- Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Section 3.
