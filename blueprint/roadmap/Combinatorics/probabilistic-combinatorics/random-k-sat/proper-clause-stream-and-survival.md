# Proper-clause streams, survival and first failure

A clause is a chosen $k$-element subset of variables with a Boolean sign defined on that subset. Give the finite set of clauses its uniform law and the full clause sequence the infinite product law. Given a finite set $S$ of assignments, survival of the first $g$ clauses means some $a\in S$ satisfies each clause before $g$; the block-kill probability is the probability of the complementary event. The clause-step operator on functions of assignment sets takes the finite average of the value after restricting $S$ to the assignments satisfying the drawn clause. At time zero use the nonempty-set indicator. Its $m$th iterate defines the survival value, and the lifetime is the totalized real sum of those values over $m\ge0$.

For the first-failure model take $S$ to be all assignments. The first failing prefix order is the infimum in extended naturals of the failing prefix lengths, with infinity if there is none. Apply clipping at the natural floor of $Bn$ before conversion to the reals when clipping is specified; the unbounded model uses the natural projection of the extended order. The variance is the real projection of the extended nonnegative variance.

## Sources

- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SATSharpness.lean#L13-L56)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SATVariance.lean#L11-L52)
