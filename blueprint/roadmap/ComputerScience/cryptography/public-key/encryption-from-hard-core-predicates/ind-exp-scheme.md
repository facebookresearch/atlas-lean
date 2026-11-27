# Distinguishing encryptions is distinguishing the hard-core bit

For the [scheme](scheme.md), the
[indistinguishability experiment](../../security-games/semantic-security-and-indistinguishability/ind-exp.md) on the bit $\sigma$ is the
[hard-core experiment](hc-exp.md) in world $\sigma$: the ciphertext $(p_\alpha(r), \sigma \oplus b(r))$
is the pair $(p_\alpha(r), b(r))$ or $(p_\alpha(r), \lnot b(r))$.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.3.4, proof of Proposition 5.3.14.
