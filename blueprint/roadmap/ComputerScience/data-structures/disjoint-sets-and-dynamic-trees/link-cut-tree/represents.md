# Representation by ordered auxiliary trees

The reference state is valid, its roots have
identity weight and its vertices are exactly the allocated handles. Every maximal preferred
path is the inorder traversal of a stored auxiliary tree with consistent reverse pointers,
edge payloads and caches. Its root's up-pointer is the represented parent of the first vertex
of the path, or null at a represented root. Thus the auxiliary trees cover the handles
disjointly, in path order rather than handle order.
