# Replacing the child edge for a symbol

Given a symbol $c$, an edge $e$ (a pair of a label
and a radix trie) and a list of child edges, this operation replaces the first edge of the list
whose label starts with $c$ by $e$ and keeps all other edges in order. If no label in the list
starts with $c$, it appends $e$ at the end of the list.
