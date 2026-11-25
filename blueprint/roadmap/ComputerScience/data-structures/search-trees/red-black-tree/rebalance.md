# Rebuilding a red-black tree from its keys

For a linearly ordered key type, the rebuild of
a red-black tree $t$ is the tree obtained from the empty tree by inserting the keys of the inorder
traversal of $t$ one at a time with Okasaki insertion, starting from the last key.

The result is a valid red-black tree whose keys are exactly the keys of $t$.
