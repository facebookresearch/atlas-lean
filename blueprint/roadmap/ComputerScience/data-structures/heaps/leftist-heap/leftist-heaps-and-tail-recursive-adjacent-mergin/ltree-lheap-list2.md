# List-to-heap construction gives a leftist tree

Over a linear order, for every list $L$, the leftist heap built from $L$ by tail-recursive
adjacent merging satisfies the leftist invariant: at every node the stored rank is one plus the
rank of the right subheap, and the rank of the left subheap is at least that of the right subheap.
