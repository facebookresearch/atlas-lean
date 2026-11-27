# Big-endian decoding of a bit string

The big-endian decoding of a bit string $l = (l_0, \dots, l_{k-1})$ is the natural number
$\sum_{i < k} l_i \, 2^{k - 1 - i}$, whose binary digits, most significant first, are the entries of $l$.
It inverts the fixed-width encoding (Katz and Lindell, 2nd ed., Section 11.5).
