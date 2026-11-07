# Restricted Gaussian partition

Let $q$ and $n$ be natural numbers and let $G$ be a
Gaussian partition. Then $G$ is a restricted Gaussian partition for $q$ and $n$ when $q$ is a
prime power, $n > 0$, and there exist blocks $(d_1, m_1), \dots, (d_\ell, m_\ell)$ and, for each
block $i$, a chain $C_i$ of branch steps $(a, b, c)$, with the following properties.

The blocks satisfy $d_i \ge 1$ and $m_i \ge 1$ for every $i$, $d_1 > d_2 > \dots > d_\ell$ and
$m_1 d_1 + \dots + m_\ell d_\ell = n$. With $p_i = \sum_{h < i} m_h d_h$, the basic segment of
block $i$ is the list of $\beta_i = \sum_{j=0}^{m_i - 1} q^{p_i + j d_i}$ copies of $d_i$.

Each chain $C_i$ is empty or satisfies the following: its first step $(a, b, c)$ has
$1 \le b \le a$, $a + b = d_i$, $1 \le c \le q^{p_i + (m_i - 1) d_i} - 1$ and $\beta_i \ne 1$,
and each pair of consecutive steps $(a, b, c), (a', b', c')$ has $a' + b' = a$,
$1 \le b' \le a'$ and $1 \le c' \le c$.

A step $(a, b, c)$ acts on a list of dimensions by deleting its last $c$ entries equal to
$a + b$ and putting $c$ copies of $a$ followed by $c q^a$ copies of $b$ where the first deleted
entry was, after the entries before it and before the remaining entries after it; it fails if
the list has fewer than $c$ entries equal to $a + b$. Applying the steps of $C_i$ in order to the
basic segment of block $i$ succeeds for every $i$, with final segment $F_i$.

The concatenation of the basic segments is nonincreasing, the concatenation $F_1 \cdots F_\ell$
is nonincreasing, and for every block $i$ and every $k$ smaller than the length of $C_i$, the
concatenation of $F_1, \dots, F_{i-1}$, the result of applying the first $k + 1$ steps of $C_i$
to the basic segment of block $i$, and the basic segments of blocks $i + 1, \dots, \ell$ is
nonincreasing. Finally, the dimension list of $G$ is $F_1 \cdots F_\ell$.
