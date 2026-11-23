# The hybrid reduction at position $j$

From a distinguisher $D$ for $\ell$-bit ciphertexts, a message $u$ and a position $j$: on the public
key $y$, a residuosity challenge $z$ and coins $(r, x_1, \dots, x_\ell)$, encrypt $u$ bitwise with
randomness $x$, replace the $j$-th component by $z$ (if $u_j = 0$) or by $y z$ (if $u_j = 1$), and run
$D$ with coins $r$. One call to $D$ and $\ell$ encryptions of single bits.
