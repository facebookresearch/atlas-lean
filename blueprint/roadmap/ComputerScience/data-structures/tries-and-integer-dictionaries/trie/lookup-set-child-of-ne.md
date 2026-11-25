# Setting a child leaves the other children unchanged

Let $L$ be a list of letter–trie
pairs, $c$ a trie and $a \ne b$ letters, and let $L'$ be obtained from $L$ by setting the child
at $b$ to $c$ (removing the entries at $b$ instead when $c$ has neither value nor children).
Then looking up $a$ in $L'$ gives the same result as looking up $a$ in $L$.
