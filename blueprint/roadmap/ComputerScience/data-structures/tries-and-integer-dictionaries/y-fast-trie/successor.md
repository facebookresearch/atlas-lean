# Successor query in a grouped y-fast trie

For a grouped y-fast trie $t$ and a key
$x$, let $r$ be the least key greater than $x$ stored in the representative x-fast trie of
$t$; if there is none, the query returns nothing. Otherwise let $g$ be the first group of $t$
whose last element is $r$, or the empty list if no group has last element $r$. The query then
returns the first key of $g$ greater than $x$, or nothing if $g$ has no such key.
