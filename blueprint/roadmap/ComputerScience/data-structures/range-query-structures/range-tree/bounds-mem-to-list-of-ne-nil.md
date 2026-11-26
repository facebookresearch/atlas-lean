# The cached bounds of a nonempty bounds-valid range tree are leaf values

Let $t$ be a
bounds-valid range tree with at least one leaf. Then the cached lower bound of $t$ and the cached
upper bound of $t$ are both leaf values of $t$.

Together with the fact that every leaf value lies between the cached bounds, this shows that the
cached interval is exactly the interval spanned by the leaves, not merely an enclosing one.
