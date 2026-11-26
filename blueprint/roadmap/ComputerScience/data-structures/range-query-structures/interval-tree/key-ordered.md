# Key-ordered interval tree

The empty tree is key-ordered, and a node is key-ordered when
both of its subtrees are key-ordered, the key of every entry in the left subtree is strictly less
than the key of the node's entry, and the key of the node's entry is strictly less than the key of
every entry in the right subtree. Keys are compared lexicographically: low endpoint first, then
identifier.
