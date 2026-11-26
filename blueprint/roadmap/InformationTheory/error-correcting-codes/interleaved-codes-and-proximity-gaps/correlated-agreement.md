# Correlated agreement of a tuple of words with a code

Let $C \subseteq \mathbb{F}^n$ be a linear code over a field and $e \le n$. Words $u_0, \dots, u_\ell \in \mathbb{F}^n$ have $e$-correlated agreement with $C$ if there exist a single coordinate set $D' \subseteq [n]$ with $|D'| \ge n - e$ and codewords $v_0, \dots, v_\ell \in C$ such that $u_j$ and $v_j$ agree on $D'$ for every $j$. Equivalently, the matrix with rows $u_0, \dots, u_\ell$ lies within Hamming distance $e$ of the interleaved code $C^{\{0, \dots, \ell\}}$. Correlated agreement implies that every linear combination $\sum_j z_j u_j$ is within distance $e$ of $C$; proximity-gap theorems give converses for structured families of combinations (lines $u_0 + z u_1$, curves $\sum_j z^j u_j$, and affine spaces $u_0 + \sum_j z_j u_j$).

## Depends on

- [Interleaved linear codes](interleaved-linear-code.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
