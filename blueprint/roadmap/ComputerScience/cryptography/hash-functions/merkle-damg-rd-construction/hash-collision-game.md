# Hash collision game for Merkle–Damgård

Let $H$ be the Merkle–Damgård hash with length
strengthening defined by a compression function $h : S \times B \to S$, an initial value
$iv \in S$ and a length encoding $\ell : \mathbb{N} \to B$, and let $N$ be a natural number. An
adversary $A$ maps random coins $r$ from a finite nonempty type $R$ to a pair of lists of blocks.
The game is the distribution of the Boolean outcome when $r$ is drawn uniformly from $R$: the
adversary wins (outcome true) exactly when $A(r) = (M, M')$ with $M \ne M'$, both $M$ and $M'$
have fewer than $N$ blocks, and $H(M) = H(M')$.
