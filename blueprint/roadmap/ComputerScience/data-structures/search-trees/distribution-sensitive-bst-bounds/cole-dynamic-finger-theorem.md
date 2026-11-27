# Cole's dynamic finger theorem for splay trees

For every initial splay tree on $n$ keys and every access sequence $X$ of length $m$ on those keys, the total cost of serving $X$ by splaying is $O(m + n + \mathrm{DF}(X))$, settling Sleator and Tarjan's dynamic finger conjecture.

## Proof sketch

The proof spans two papers. Cole, Mishra, Schmidt and Siegel first analyze splay sorting of sequences made of $\log n$ blocks of keys, and Cole then completes the argument with an intricate amortized analysis that charges $O(\log(d+2))$ amortized rotations to an access at key distance $d$ from the previous access, grouping accesses by the scale $\lceil \log_2 d \rceil$ of their distances.

## Depends on

- [Dynamic finger bound](dynamic-finger-bound.md)
- [Splay operation](../splay-tree/splay.md)

## Sources

- Richard Cole, "On the Dynamic Finger Conjecture for Splay Trees. Part II: The Proof", SIAM Journal on Computing 30(1) (2000).
- Richard Cole, Bud Mishra, Jeanette Schmidt, Alan Siegel, "On the Dynamic Finger Conjecture for Splay Trees. Part I: Splay Sorting log n-Block Sequences", SIAM Journal on Computing 30(1) (2000).
