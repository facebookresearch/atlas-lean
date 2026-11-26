# Van der Waerden forcing number for intervals starting at zero

For natural numbers $r,k,N$, say $N$ forces a progression if for every coloring $c:\mathbb N\to[r]$ there are naturals $a,d$ with $d>0$ and $a+(k-1)d<N$, such that $c(a+jd)=c(a)$ for all $j<k$. Here $[r]=\{0,\ldots,r-1\}$ and natural subtraction is truncated. Define $W(r,k)$ to be the infimum in $\mathbb N$ of the set of **positive** forcing sizes $N$. Where that set is nonempty, this is its least element. The natural infimum of the empty set is zero; this convention does not assert attainment there.

## Related topics

- [Van der Waerden's theorem](van-der-waerden.md) uses the equivalent interval beginning at one when $r$ and $k$ are positive; translating an interval does not change its cardinality.

## Sources

- OpenAI, [Progressions and natural infimum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/Model.lean#L9-L21).
