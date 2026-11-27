# The indistinguishability experiment

Let $S$ be a public-key encryption scheme with key generation $\mathrm{Gen}$ and probabilistic
encryption $\mathrm{Enc}$. For a distribution of random coins on a type $R$, a distinguisher $D$, which
maps a public key, a ciphertext and coins to a bit, and a message $m$, the indistinguishability
experiment draws a key pair $(pk, sk) \leftarrow \mathrm{Gen}$, coins $r$ and a ciphertext
$c \leftarrow \mathrm{Enc}_{pk}(m)$, and outputs $D(pk, c, r)$.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Definition 5.2.4 (the public-key form, in which the distinguisher receives the encryption key).
