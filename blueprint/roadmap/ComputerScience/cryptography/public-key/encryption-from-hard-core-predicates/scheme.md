# Encryption of one bit with a hard-core predicate

Let key pairs $(\alpha, \tau)$ be drawn from a distribution, let $p_\alpha$ be a permutation of a
finite nonempty domain $D$, let $\mathrm{inv}_\tau$ be a function on $D$ (the trapdoor inverse) and
let $b_\alpha$ be a predicate on $D$. The public key is $\alpha$ and the secret key is
$(\alpha, \tau)$. A bit $\sigma$ is encrypted as $(p_\alpha(r), \sigma \oplus b_\alpha(r))$ for a
uniform $r \in D$, and a ciphertext $(y, \varsigma)$ is decrypted as
$\varsigma \oplus b_\alpha(\mathrm{inv}_\tau(y))$.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.3.4, Construction 5.3.13 (where the domain is sampled by an algorithm $S(\alpha)$; here it is a
  fixed finite type).
