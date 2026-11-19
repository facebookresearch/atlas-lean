# Looking up a child just set

Let $L$ be a list of letter–trie pairs, $a$ a letter and
$c$ a trie, and let $L'$ be obtained from $L$ by setting the child at $a$ to $c$ (removing the
entries at $a$ instead when $c$ has neither value nor children). Looking up $a$ in $L'$ finds
nothing when $c$ has neither value nor children, and finds $c$ otherwise.
