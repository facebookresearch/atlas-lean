# Running a POP agrees with the standalone POP

For every stack $S$ and every finite
sequence $\sigma$ of stack operations, running POP followed by $\sigma$ on $S$ has the same result
and cost as first performing the standalone POP on $S$ and then, if it reports underflow,
stopping with an error at no further cost, or, if it removes the top element and leaves the stack
$S'$, running $\sigma$ on $S'$, the two costs being added.
