# Bottom-up heap construction with comparison and swap counts

For an array $a$ of length
$n$ over a linearly ordered type, the timed construction runs timed sift-down from the positions
$i = \lfloor n/2 \rfloor - 1, \dots, 1, 0$ in turn, each on the array the previous one returned,
and returns the last array together with the componentwise sum of their cost pairs
(value comparisons, array swaps).
