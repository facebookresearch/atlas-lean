# Indistinguishability is unattainable against unbounded distinguishers

Let a public-key scheme be correct, and let $m \ne m'$ be messages of the same length. Then for every
distribution of coins and every $\varepsilon < 1$, the scheme does not have
[indistinguishable encryptions with error $\varepsilon$](ind-secure.md) in this concrete model. The
distinguisher that outputs $1$ exactly when some secret key matching the public key decrypts the
ciphertext to $m'$ outputs $1$ on every encryption of $m'$ and never on an encryption of $m$: by
correctness, every key pair with that public key decrypts encryptions of $m$ to $m$. Its advantage is
therefore $1$.

This holds for probabilistic as well as deterministic encryption: it is the reason the computational
definitions restrict distinguishers to efficient ones.

## Informally uses

- [A game that never outputs `¬ b` always outputs `b`](../games-and-advantages/eq-pure-of-not-mem-support.md)
