# Failed open-addressing insertion finds every probed slot taken

Let $T$ be an
open-addressing hash table with $m$ slots and probe sequence $p$. If inserting a binding
$k \mapsto v$ into $T$ fails, then for every $i < m$ the slot $p(k, i)$ holds a pair
$(k', v')$ with $k' \neq k$.

For probe sequences that are permutations of the slots, this says that every slot of the table
holds a key other than $k$.
