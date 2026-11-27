# Correctness of encryption with a hard-core predicate

If $\mathrm{inv}_\tau(p_\alpha(x)) = x$ for every $x$ and every key pair $(\alpha, \tau)$ in the support
of the key distribution, then the [scheme](scheme.md) is correct: every ciphertext of a bit decrypts
to that bit.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.3.4, the computation following Construction 5.3.13.
