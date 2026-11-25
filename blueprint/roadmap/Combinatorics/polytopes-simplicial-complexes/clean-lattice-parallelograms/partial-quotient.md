# Partial quotients of a rational number

Let $x$ be a rational number. The continued
fraction algorithm sets $x_0 = x$ and $q_0 = \lfloor x_0 \rfloor$ and, as long as $x_j$ is not an
integer, $x_{j+1} = 1/(x_j - q_j)$ and $q_{j+1} = \lfloor x_{j+1} \rfloor$; it stops at the first
index $m$ for which $x_m$ is an integer, so that $x = [q_0; q_1, \dots, q_m]$. For a natural
number $i$, the $i$-th partial quotient of $x$ is $q_i$ when $i \le m$ and $0$ when $i > m$.

## Sources

- Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10, Section 3.
