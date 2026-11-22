# Setting a child preserves the child-list part of validity

Let $L$ be a list of
letter–trie pairs whose letters are pairwise distinct and whose tries are all valid, let $c$
be a valid trie and $a$ a letter. Then the list obtained from $L$ by setting the child at $a$
to $c$ (removing the entries at $a$ instead when $c$ has neither value nor children) again has
pairwise distinct letters, and every trie in it is valid.
