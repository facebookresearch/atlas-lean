# Bottom-up heap construction

For an array $a$ of length $n$ over a linearly ordered type,
bottom-up construction sifts down the positions $i = \lfloor n/2 \rfloor - 1, \dots, 1, 0$ in
turn, each time continuing with the array the previous sift-down returned. When $n \le 1$ there
is no such position and the result is $a$.
