# Piece of an n-bit swap with i antisymmetric factors

Let $n, i \in \mathbb{N}$, and index rows and columns by pairs $(x, y)$ of $n$-bit strings
$x, y \in \{0, 1\}^n$. The $i$-th piece of the $n$-bit swap is the integer matrix $\Pi_{n,i}$ with
entries

$$\Pi_{n,i}\bigl[(x, y), (u, v)\bigr] = \sum_{\substack{S \subseteq \{1, \dots, n\} \\ |S| = i}}
\ \prod_{k \in S} \bigl(-s(x_k, y_k)\, s(u_k, v_k)\bigr) \prod_{k \notin S}
\bigl[(x_k, y_k) = (u_k, v_k)\bigr],$$

where $s$ is the [antisymmetric two-bit vector](bit-singlet.md) and $[\cdot]$ is $1$ if the
condition holds and $0$ otherwise. It collects the terms with exactly $i$ antisymmetric factors in
the expansion of the bitwise product of the [one-bit identities](bit-swap-eq-one-sub-vec-mul-vec.md)
$I - s s^{\mathsf{T}}$.
