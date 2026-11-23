# Deletion preserves lookups below the last position

Let $T$ be a well-formed dynamic
table holding $n$ items, and let $i$ be a natural number with $i < n - 1$. After applying
deletion to $T$, the lookup at logical position $i$ returns the same result as the lookup at
position $i$ in $T$.
