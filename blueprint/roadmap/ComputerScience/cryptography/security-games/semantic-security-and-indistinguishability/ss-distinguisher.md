# The distinguisher hardwiring one plaintext

For an adversary $A$, functions $h$ and $f$ and a plaintext $x$, this distinguisher maps a public key
$pk$, a ciphertext $c$ and coins $r$ to the bit $[A(pk, c, h(x), r) = f(x)]$. The values $h(x)$ and
$f(x)$ are built in, which is why no computability assumption on $h$ or $f$ is needed.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, proof of Proposition 5.2.6, Claim 5.2.6.1 (the circuit $C_n$).
