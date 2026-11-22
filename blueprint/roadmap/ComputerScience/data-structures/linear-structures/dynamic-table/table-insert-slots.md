# Slots after an insertion

Let $T$ be a well-formed dynamic table with slots
$s_0, \dots, s_{m-1}$ and item count $n$, let $x$ be an item, and let $T'$ be the table returned
by inserting $x$ into $T$ with TABLE-INSERT, with capacity $m'$. Then the slots of $T'$ are
$s_0, \dots, s_{n-1}$, followed by a slot holding $x$, followed by $m' - (n + 1)$ empty slots.
