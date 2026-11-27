# The real semantic-security experiment

For a public-key encryption scheme, a distribution of coins, an adversary $A$ (a function of the
public key, a ciphertext, a priori information and coins, with values in a type $T$ of guesses), a
plaintext distribution $X$, an a priori information function $h$ and a target function $f$, the
experiment draws $x \leftarrow X$, a key pair, coins $r$ and a ciphertext
$c \leftarrow \mathrm{Enc}_{pk}(x)$, and outputs whether $A(pk, c, h(x), r) = f(x)$.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Definition 5.2.2 (the first probability, in the public-key form).
