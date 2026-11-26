# Characterization of the Bloom filter false-positive event

Let $H$ be a list of hash functions from a type $\alpha$ to $\{0, \dots, m - 1\}$, let $L$ be a
list of elements of $\alpha$ and let $y \in \alpha$. The filter obtained by inserting the elements
of $L$ into the empty Bloom filter with hash functions $H$ reports that $y$ may be present if and
only if for every $h$ in $H$ there are an element $x$ of $L$ and some $h'$ in $H$ with
$h'(x) = h(y)$.
