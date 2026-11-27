# Call trace of a point update

A point update at a natural-number index $i$ stops on
an empty tree or at a leaf. It calls just the left child at $i$ when $i\lt m$ for left size
$m$, and just the right child at $i-m$ otherwise, using truncated natural subtraction.
The trace does not depend on the replacement value. There is no out-of-range guard at
internal nodes.
