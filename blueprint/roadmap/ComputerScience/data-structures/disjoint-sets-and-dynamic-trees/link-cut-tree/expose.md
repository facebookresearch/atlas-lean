# Physical access in a link-cut forest

Splay the current handle, switch its right child
and follow its path-parent, successively joining the path segments. Finally splay the original
target in the joined path. All iterations, including those requiring no rotations, are charged.
