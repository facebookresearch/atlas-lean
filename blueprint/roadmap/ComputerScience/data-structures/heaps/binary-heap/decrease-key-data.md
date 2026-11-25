# Array of a binary heap after decrease-key

Let $h$ be a binary min-heap over a linearly
ordered type, with level-order array $a$, let $i < |a|$ and let $x \le a_i$. The array of the heap
obtained by decreasing the key at position $i$ to $x$ equals the result of sifting up position $i$
in the array obtained from $a$ by replacing its entry at position $i$ with $x$.
