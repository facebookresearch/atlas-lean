# A Merkle–Damgård hash collision yields a compression collision

Let
$h : S \times B \to S$ be a compression function, $iv \in S$ an initial value and
$\ell : \mathbb{N} \to B$ a length encoding, and let $H$ be the Merkle–Damgård hash with length
strengthening they define. Write $|M|$ for the number of blocks of a list of blocks $M$. If $M$
and $M'$ are distinct lists of blocks with $H(M) = H(M')$, and $\ell(|M|) = \ell(|M'|)$ implies
$|M| = |M'|$, then the collision-finding procedure applied to $M$ and $M'$ returns a pair
$(p_1, p_2)$ of compression inputs with $p_1 \ne p_2$ and $h(p_1) = h(p_2)$.

This is a block-level form of Katz and Lindell, Theorem 5.4.
