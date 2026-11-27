# Setting a child preserves validity

Let a trie node with value $v$ and child list $L$ be
valid, let $c$ be a valid trie and $a$ a letter. Then the node with value $v$ whose child list
is obtained from $L$ by setting the child at $a$ to $c$ (removing the entries at $a$ instead
when $c$ has neither value nor children) is valid.
