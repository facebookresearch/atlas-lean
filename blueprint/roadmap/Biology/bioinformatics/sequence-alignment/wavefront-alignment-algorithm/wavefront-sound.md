# Soundness of the wavefront algorithm

If the [wavefront offset](wavefront.md) $W(s, k)$ is $h$, then

- $\max(0, k) \le h \le \min(|y|, |x| + k)$;
- some [valid alignment](../pairwise-sequence-alignment/is-alignment.md) of the first $h - k$ letters of $x$ and the first $h$ letters of $y$ has [cost](cost.md) at most $s$.
