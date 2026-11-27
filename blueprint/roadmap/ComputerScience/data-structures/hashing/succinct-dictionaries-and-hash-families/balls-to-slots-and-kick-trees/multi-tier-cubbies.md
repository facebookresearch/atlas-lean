# Multi-tier full cubbies with a tail cubby

In the dynamically resized $k$-kick tree dictionary, keys are hashed to *facilities* of $\Theta(K)$ keys, $K = \mathrm{polylog}\, N$, and each facility stores its keys in *cubbies*: fixed-capacity dictionaries whose slots are organized by a $k$-kick tree. A cubby is *$j$-tiered*, for $j \in [1, k]$, if its capacity is $r_j = K/(\log^{(j)} n)^2$, so $r_1 < r_2 < \dots < r_k$ and $r_{j+1} = t_j r_j$ with tier ratio $t_j = (\log^{(j)} n)^2/(\log^{(j+1)} n)^2$ for $j < k$. One 1-tiered cubby is the *tail*, and the *saturation invariant* requires every other cubby to be completely full (no empty slot). It is maintained as follows: an insertion into the facility goes to the tail; a deletion from a non-tail cubby is followed by moving a randomly chosen item of the tail into that cubby; when the tail fills up it becomes an ordinary full 1-tiered cubby and a new empty tail is created; when the tail empties it is eliminated and another 1-tiered cubby becomes the tail. The *distribution invariant* keeps $\Theta(t_j)$ cubbies of each tier $j < k$: when fewer than $t_j/2$ are $j$-tiered, one $(j+1)$-tiered cubby is rebuilt as $t_j$ full $j$-tiered cubbies (a $j$-creation rebuild), and when more than $3 t_j$ are $j$-tiered, $t_j$ of them are rebuilt as one $(j+1)$-tiered cubby (a $j$-destruction rebuild), with the items partitioned at random.

## Depends on

- [k-kick tree balls-to-slots scheme](k-kick-tree.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602 (Section 5.2).
