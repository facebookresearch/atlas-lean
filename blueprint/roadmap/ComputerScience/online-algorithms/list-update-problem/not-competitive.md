# No deterministic online list-update algorithm beats $2 - 2/(\ell + 1)$

Let $M$ be a
nonempty list of $\ell$ distinct items and let $A$ be a deterministic online list-update
algorithm on the items of $M$. Let $c$, $d$ and $b$ be natural numbers with
$c (\ell + 1) < 2 \ell d$ (so $d \ge 1$ and $c / d < 2\ell / (\ell + 1) = 2 - 2/(\ell + 1)$).
Then there are a request sequence $\sigma$, each request an item of $M$, and lists
$L_0, L_1, L_2, \dots$, each a rearrangement of $M$, with $L_0 = M$, such that
$c \cdot C + d \cdot b < d \cdot K$, where $C$ is the offline cost without free exchanges of
$L_0, L_1, \dots$ on $\sigma$ and $K$ is the cost of $A$ on $\sigma$ from its initial state.

The offline lists make no free exchanges, so the same holds with the offline cost with free
exchanges in place of $C$.

## Sources

- Karp and Raghavan, see Irani, *Two results on the list update problem*, IPL 38, 1991; Borodin and El-Yaniv, Chapter 1.
