# Binary Chvátal–Sankoff constant

Let $L_n$ be the length of a longest common subsequence
of two independent uniformly random binary strings of length $n$. The binary Chvátal–Sankoff
constant is the real number $\liminf_{n \to \infty} \mathbb{E}[L_n]/n$.

For every $n \ge 1$ the quotient $\mathbb{E}[L_n]/n$ lies in $[0, 1]$, so this limit inferior is
finite. By the theorem of Chvátal and Sankoff the sequence converges, so the constant equals the
ordinary limit $\lim_{n \to \infty} \mathbb{E}[L_n]/n$; defining it as a limit inferior avoids
choosing an arbitrary value before convergence is known.
