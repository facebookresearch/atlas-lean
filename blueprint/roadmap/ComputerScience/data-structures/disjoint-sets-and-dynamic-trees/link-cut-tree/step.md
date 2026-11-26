# Costed link-cut operation on handles

Link exposes both arguments and puts the second
on the left of the first. Cut exposes its target, removes its left subtree and resets its edge
weight to the identity. Find-root exposes, walks left, then splays the vertex it returns.
A path query exposes and reads one cache. The caller supplies legal arguments; the pointer
machine does not validate global connectivity by a free search.
