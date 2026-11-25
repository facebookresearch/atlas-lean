# CRC codec

For a field $F$ and a nonzero generator polynomial $g$ of degree $r$, the codec on polynomials over $F$ with alphabet $F$: a message $m$ is encoded as the coefficient list, constant term first, of its CRC codeword $m X^r - (m X^r \bmod g)$. A word is decoded by reading it as a polynomial (constant term first); it is rejected unless $g$ divides that polynomial, and otherwise the message is the polynomial left after dropping its $r$ lowest coefficients.
