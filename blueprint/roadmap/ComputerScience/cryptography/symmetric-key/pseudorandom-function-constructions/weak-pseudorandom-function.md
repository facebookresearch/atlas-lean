# Weak pseudorandom function

A keyed family $F_k : \{0,1\}^n \to \{0,1\}^{m}$ is a *weak PRF* if every efficient adversary has negligible advantage in distinguishing an oracle that, on each call, returns a fresh uniform $x \in \{0,1\}^n$ together with $F_k(x)$ (for a uniform key $k$) from one returning $x$ together with $f(x)$ for a uniformly random function $f$. The adversary never chooses the inputs. Every PRF is a weak PRF; the converse fails if PRFs exist.

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Sources

- M. Naor and O. Reingold, "Number-Theoretic Constructions of Efficient Pseudo-Random Functions", Journal of the ACM 51(2), 2004.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
