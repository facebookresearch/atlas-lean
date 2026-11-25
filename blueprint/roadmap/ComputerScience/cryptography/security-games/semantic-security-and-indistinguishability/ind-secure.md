# Indistinguishability of encryptions with error $\varepsilon$

A public-key encryption scheme, with a length function on its messages and a distribution of the
adversary's coins, has indistinguishable encryptions with error $\varepsilon$ if for every
distinguisher $D$ (a function of the public key, the ciphertext and the coins) and all messages
$m, m'$ of the same length, the
[distinguishing advantage of $D$ between encryptions](ind-advantage.md) of $m$ and $m'$ is at most
$\varepsilon$.

This is Goldreich's Definition 5.2.4 in concrete form: the error $1/p(n)$ "for every positive
polynomial $p$ and all sufficiently large $n$" is replaced by one number $\varepsilon$, and every
function is an admissible distinguisher, where Goldreich quantifies over polynomial-size circuit
families. In this concrete model every function counts as an adversary, so no correct public-key scheme with two distinct messages of the same length meets it with $\varepsilon < 1$, deterministic or probabilistic
([unattainability](not-ind-secure-of-correct.md)): a distinguisher may decrypt with any secret key
matching the public key. With a small $\varepsilon$ the definition therefore describes
information-theoretic security; for public-key schemes the content lies in the per-adversary
statements, such as [indistinguishability implies semantic security, per
adversary](win-prob-ss-real-le.md), which carry over to efficient adversaries.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Definition 5.2.4.
