# Open-addressing insertion leaves other keys' bindings unchanged

Let $T$ be an
open-addressing hash table, and suppose that inserting the binding $k \mapsto v$ into $T$
succeeds and yields the table $T'$. Then for every key $k' \neq k$ and every value $v'$, the
table $T'$ stores $k' \mapsto v'$ if and only if $T$ stores $k' \mapsto v'$.

No validity assumption is needed: the insertion writes a single slot, previously empty or
previously holding $k$, and leaves every other slot unchanged.
