# Correlated agreement for random lines within one third of the minimum distance

Let $C \subseteq \mathbb{F}^n$ be a linear code over a field with minimum distance greater than $3e$. If $u_0, u_1 \in \mathbb{F}^n$ and $S \subseteq \mathbb{F}$ is a set of more than $e + 1$ scalars such that $u_0 + z u_1$ is within Hamming distance $e$ of $C$ for every $z \in S$, then $u_0, u_1$ have $e$-correlated agreement with $C$. Consequently, over a finite field, either $u_0 + z u_1$ is $e$-close to $C$ for at most $e + 1$ values of $z$, or the pair is $e$-close to the interleaved code; the same holds for random combinations $\sum_r z_r W_r$ of the rows of an interleaved word, where the $e$-close matrices have at most one nearby interleaved codeword.

## Proof sketch

Take two scalars $z \ne z'$ in $S$ with nearby codewords $c, c'$; solving the two equations gives candidate codewords $v_1 = (c - c')/(z - z')$ and $v_0 = c - z v_1$. For any third $z''$, the codeword near $u_0 + z'' u_1$ must equal $v_0 + z'' v_1$, because both are within $3e$ of each other on the common agreement region; more than $e + 1$ scalars then force the error positions to be shared.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
