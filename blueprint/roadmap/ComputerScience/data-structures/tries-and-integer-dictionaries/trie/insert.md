# Trie insertion

Inserting a value $v$ at a key $k$ (a list of letters) in a trie stores $v$
at the node reached by following $k$ from the root, replacing any value stored there. Along the
way, a missing child is created as an empty trie and appended after its siblings, an existing
child is updated in place, and all other values and children are unchanged.
