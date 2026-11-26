# Cole's dynamic finger theorem for splay trees

For every access sequence $X$ of length $m$ on $n$ keys, the total cost of splay trees on $X$ is $O(m + n + \mathrm{DF}(X))$, settling Sleator and Tarjan's dynamic finger conjecture.

## Proof sketch

Cole's proof partitions the accesses by the scale $\lceil \log_2 |x_t - x_{t-1}| \rceil$, analyzes splaying of a key near the previous root via a hierarchy of *guards* and the effect of rotations on intervals of keys at each scale, and uses an intricate potential argument, building on the splay sequential-access theorem, to charge $O(\log(d+2))$ amortized rotations to an access at key distance $d$.

## Depends on

- [Dynamic finger bound](dynamic-finger-bound.md)
- [Splay operation](../splay-tree/splay.md)

## Proof depends on

- [Dynamic finger bound](dynamic-finger-bound.md)
- [Splay operation](../splay-tree/splay.md)

## Sources

- Richard Cole, "On the Dynamic Finger Conjecture for Splay Trees. Part II: The Proof", SIAM Journal on Computing 30(1) (2000).
