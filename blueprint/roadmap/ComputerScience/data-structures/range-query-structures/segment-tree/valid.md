# Valid segment trees

Validity of a segment tree over an additive monoid is defined
inductively: the empty tree and every leaf are valid, and an internal node with valid left child
$L$ and valid right child $R$ is valid when its cached aggregate is the aggregate of $L$ plus
the aggregate of $R$ and its cached length is the size of $L$ plus the size of $R$. Here the
aggregate and size of the empty tree are $0$ and $0$, of a leaf with value $x$ are $x$ and $1$,
and of an internal node are its cached aggregate and cached length.
