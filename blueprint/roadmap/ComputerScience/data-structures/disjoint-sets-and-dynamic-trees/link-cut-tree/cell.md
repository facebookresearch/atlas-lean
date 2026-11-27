# Link-cut vertex record

A record at a stable handle stores two ordinary auxiliary
children and an up-pointer. If its target does not list this handle as a child, the pointer is
a path-parent pointer. The payload is the incoming represented edge weight (identity at a
represented root); the cache is the ordered product for the auxiliary subtree.
