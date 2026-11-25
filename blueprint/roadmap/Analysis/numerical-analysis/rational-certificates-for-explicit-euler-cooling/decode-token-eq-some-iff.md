# Token decoding inverts admissible token encoding

For a list of characters $cs$ and $q \in \mathbb{Q}$, token decoding of $cs$ returns $q$ if and only if there is an admissible token $t$ with $cs$ equal to the characters of $t$ and $q$ equal to the value of $t$.

An admissible token is a character string $[-]n/d$ (an optional minus sign, a run $n$ of digits, a slash, a run $d$ of digits) in which both digit runs have one to eleven ASCII decimal digits (leading zeros allowed), the signed numerator has absolute value at most $10^{10}$, and the denominator lies in $[1, 10^{10}]$; its value is the rational numerator$/$denominator.
