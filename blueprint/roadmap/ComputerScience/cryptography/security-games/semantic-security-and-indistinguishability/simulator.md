# The simulator of Goldreich's Proposition 5.2.6

Given an adversary $A$ and a dummy message $\mathrm{dummy}(n)$ for each length $n$, the simulator,
on a length $n$ and a priori information $v$, draws a key pair, coins $r$ and a ciphertext
$c \leftarrow \mathrm{Enc}_{pk}(\mathrm{dummy}(n))$, and outputs $A(pk, c, v, r)$. It runs $A$ once on
an encryption of a dummy message instead of the real plaintext; Goldreich uses $1^{|\alpha|}$ as the
dummy.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, proof of Proposition 5.2.6 (Section 5.2.3.1, the construction of $A'$).
