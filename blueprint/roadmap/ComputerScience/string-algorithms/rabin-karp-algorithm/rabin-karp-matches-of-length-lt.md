# Rabin–Karp matching with a pattern longer than the text

For every base $d$, modulus
$q > 0$ and lists of natural numbers $P$ and $T$ with $|T| < |P|$, Rabin–Karp matching of $P$ in
$T$ returns no offsets, at counted cost exactly $1 + 2(|P| - 1) + 6|T|$.

This cost is the work of computing the high-place power and the Horner setup steps attempted
before the text runs out.
