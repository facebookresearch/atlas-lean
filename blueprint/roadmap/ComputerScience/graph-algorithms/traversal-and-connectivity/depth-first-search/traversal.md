# Depth-first traversal record

A traversal over a vertex type $V$ consists of three lists: a
preorder (discovery order) list of vertices, a postorder (finish order) list of vertices, and a
list of parent pairs in $V \times V$, each stored as $(\text{child}, \text{parent})$.

No condition relating the three lists is imposed by the record itself.
