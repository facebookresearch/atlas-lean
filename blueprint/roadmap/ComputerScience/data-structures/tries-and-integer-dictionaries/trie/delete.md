# Deletion from a trie

Deleting a key $k$ (a list of letters) from a trie $t$ works by
recursion on $k$. If $k$ is empty, the root of $t$ loses its value and keeps its children. If
$k$ consists of a first letter $a$ followed by a key $k'$ and the root of $t$ has no child at
$a$, then $t$ is unchanged. Otherwise $k'$ is deleted from the first child at $a$. If the
result has neither value nor children, every entry at $a$ is removed from the root's child
list; if not, the first entry at $a$ is replaced by the result and any later entries at $a$
are removed. The root's value and the other children, in their order, are kept.

Deleting an absent key leaves every lookup unchanged.
