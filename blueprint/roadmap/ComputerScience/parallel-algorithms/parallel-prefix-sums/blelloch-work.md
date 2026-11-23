# Work of Blelloch's scan

The number $W(k)$ of monoid multiplications Blelloch's scan
performs on $2^k$ positions is defined by $W(0) = 0$ and $W(k+1) = 2^k + W(k) + 2^k$: on
$2^{k+1}$ positions, $2^k$ pair products, the recursive scan on the $2^k$ pair products, and
$2^k$ products for the odd positions.
