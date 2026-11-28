# Head-move and tail-move distances agree up to constant factors

**Setting.** Work in tier-$k$ ($k>0$) of binary phylogenetic networks on a fixed leaf set (networks with exactly $k$ reticulations). A *head move* relocates the head of an edge $(u,v)$ (the endpoint $v$) to a subdivision point of another edge; a *tail move* relocates the tail $u$ of an edge $(u,v)$ to a subdivision point of another edge. Both are allowed only when the result is again a binary phylogenetic network, and both preserve the tier. Write $d_{\mathrm{Head}}$ and $d_{\mathrm{Tail}}$ for the induced distances.

**Theorem (tail by head).** Any single valid tail move can be replaced by a sequence of at most $15$ head moves.

**Theorem (head by tail).** If a head move turns $N$ into $N'$, and $N,N'$ are not two non-isomorphic tier-1 networks on two leaves, then $N$ and $N'$ are joined by a sequence of at most $16$ tail moves.

**Corollary.** On tier-$k$ with $k>0$ and at least three leaves,

$$d_{\mathrm{Head}}(N,N')\le 15\, d_{\mathrm{Tail}}(N,N'),\qquad d_{\mathrm{Tail}}(N,N')\le 16\, d_{\mathrm{Head}}(N,N').$$

In particular, connectivity of a tier under either move type implies connectivity under the other.

## Expansion

The replacement of a tail move is a case analysis on the relative position of the source edge $(x_L,a_L)$ and target edge $(x_R,a_R)$: a horizontal move between the two children of a split node costs at most $6$ head moves, a move between the two parents of a reticulation at most $4$, and the general cases (target not above or above the source, with or without a movable reticulation edge outside the target's subtree) at most $7$ or $15$. Conversely, a distance-1 head move costs at most $4$ tail moves; a head move whose new position lies below its old one costs at most $8$; the remaining case is reduced to two such moves, giving $16$. The two-leaf tier-1 exception exists because there the only two networks are not joined by any tail move.

## Sources

- Remie Janssen, "Heading in the right direction? Using head moves to traverse phylogenetic network space", arXiv:1810.09795: Definitions 5–6; Lemmas 18–23 and Theorem 3 (tail move by at most 15 head moves); Lemmas 24–28, Propositions 1–2 and Theorem 4 (head move by at most 16 tail moves). <https://doi.org/10.48550/arXiv.1810.09795> Published version: Journal of Graph Algorithms and Applications 25 (2021) 263–310, <https://doi.org/10.7155/jgaa.00559>.
