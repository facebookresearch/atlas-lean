# Skip-list insertion does not change lookup of other keys

Let $\alpha$ be a linearly
ordered type. For every skip list $S$ with keys in $\alpha$ and values in $\beta$, all keys $k$
and $k'$ in $\alpha$ with $k' \ne k$, every value $v \in \beta$ and every requested height
$h \in \mathbb{N}$, looking up $k'$ in the skip list obtained by inserting $k$ with value $v$ and
requested height $h$ into $S$ gives the same result as looking up $k'$ in $S$.
