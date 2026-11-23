# Jordan normal form

Let $A$ be a square matrix over a field $K$, with rows and columns indexed
by a finite set $N$, whose characteristic polynomial splits into linear factors over $K$. Then $A$
is similar to a block-diagonal matrix of Jordan blocks: there are $k \in \mathbb{N}$, positive
integers $s_0, \dots, s_{k-1}$, scalars $\mu_0, \dots, \mu_{k-1} \in K$, an invertible matrix $P$
with rows and columns indexed by $N$, and a bijection $e$ from the set of pairs $(i, r)$ with
$i < k$ and $r < s_i$ onto $N$, such that $A = P J P^{-1}$, where $J$ is the block-diagonal
matrix whose $i$-th diagonal block is the Jordan block of size $s_i$ with eigenvalue $\mu_i$,
with its rows and columns relabelled by $e$.

Proof: Decompose into the maximal generalized eigenspaces (Axler, Linear Algebra Done Right,
4th ed., 8.22), take a Jordan-chain basis of each nilpotent restriction, and collect them as in
the proof of Axler 8.46. The nilpotent case is proved by induction on the range, extending chains
by preimages and adding kernel vectors, as in Wikipedia, "Jordan normal form", section "A proof".

## Sources

- R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 3.4.1.
