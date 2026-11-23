# Hadamard matrices with circulant core: Paley and twin-prime cases

Let $n$ be a natural
number such that either $n$ is a prime with $n \equiv 3 \pmod 4$, or $n = p(p + 2)$ for some
natural number $p$ with $p$ and $p + 2$ both prime. Then there is an $(n + 1) \times (n + 1)$
Hadamard matrix $H$ with integer entries, rows and columns indexed by $0, 1, \dots, n$ (so every
entry of $H$ is $1$ or $-1$ and $H^{\mathsf T} H = (n + 1) I$), that has a circulant core: there
is a function $v \colon \{0, \dots, n - 1\} \to \mathbb{Z}$ with $H_{i+1, j+1} = v(i - j)$ for
all $i, j \in \{0, \dots, n - 1\}$, where $i - j$ is taken modulo $n$.
