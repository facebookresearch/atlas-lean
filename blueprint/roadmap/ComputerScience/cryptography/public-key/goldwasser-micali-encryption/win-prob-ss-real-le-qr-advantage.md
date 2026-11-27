# Semantic security of Goldwasser–Micali for one bit, per adversary

For every adversary $A$ against the [one-bit Goldwasser–Micali scheme](scheme.md), every distribution
$X$ of the plaintext bit, every a priori information function $h$ and every target function $f$, the
probability that $A$ wins the [real semantic-security experiment](../../security-games/semantic-security-and-indistinguishability/ss-real.md) is at most the
probability that [Goldreich's simulator](../../security-games/semantic-security-and-indistinguishability/simulator.md) (which runs $A$ on an encryption of $0$)
wins the [ideal experiment](../../security-games/semantic-security-and-indistinguishability/ss-ideal.md), plus the
[residuosity advantage](qr-advantage.md) of the single distinguisher
[hardwiring the plaintext $1$](../../security-games/semantic-security-and-indistinguishability/ss-distinguisher.md), which calls $A$ once.

This is the form of Goldwasser and Micali's theorem for one bit that transfers to efficient
adversaries: an efficient $A$ gives an efficient residuosity distinguisher.

## Informally uses

- [Indistinguishability implies semantic security, for one adversary](../../security-games/semantic-security-and-indistinguishability/win-prob-ss-real-le.md)
- [Distinguishing Goldwasser–Micali ciphertexts is deciding residuosity](ind-exp-scheme.md)

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4.
- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University
  Press, 2004, Proposition 5.2.6 and Claim 5.2.6.1.
