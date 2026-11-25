# Being the maximum suffix sum

For a list $L$ over an additive monoid $\alpha$ with a
linear order, an element $e \in \alpha$ is the maximum suffix sum of $L$ when some nonempty suffix
of $L$ has sum $e$ and every nonempty suffix of $L$ has sum at most $e$. A nonempty suffix is a
contiguous run ending at the last element of $L$.

Kadane's scan maintains its first accumulator as the maximum suffix sum of the elements read
so far.
