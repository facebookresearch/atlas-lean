# Semantically secure encryption from a trapdoor function in the random oracle model

Let $T=(\mathrm{Gen},F,I)$ be a one-way trapdoor function scheme from $X$ to $Y$ (not necessarily a permutation). At each security and system parameter $(\lambda,\Lambda)$, both spaces are fixed **before** key generation: neither varies with the generated public key (Definition 10.4). Let $\mathcal{E}_s$ be a semantically secure symmetric cipher with key space $K$, and let $H : X \to K$ be a hash function modelled as a random oracle. The public-key scheme that encrypts $m$ by choosing a uniform $x \in X$ and outputting $(F(pk,x),\mathcal{E}_s(H(x),m))$ is semantically secure.

More precisely, for every adversary $A$ in the random-oracle version of Game 11.1 there are an inverter $B_{\mathrm{ow}}$ in Game 10.2 and a symmetric-cipher adversary $B_s$ in Game 2.1 such that

$$
\mathrm{Adv}^{\mathrm{SS}}_{\mathrm{ro}}[A] \le 2\cdot \mathrm{Adv}^{\mathrm{OW}}[B_{\mathrm{ow}},T] + \mathrm{Adv}^{\mathrm{SS}}[B_s,\mathcal{E}_s].
$$

Both $B_{\mathrm{ow}}$ and $B_s$ are **elementary wrappers around $A$** (Definition 2.12): each is the composition of an efficient interface with $A$. In particular, if $A$ is efficient, both are efficient. The one-way advantage is the probability of returning the sampled input. Each SS advantage is a distinguishing advantage: for $b=0,1$, let $p_b$ be the probability that the adversary outputs $1$ when its equal-length challenge messages are $m_0,m_1$ and it receives an encryption of $m_b$. Use $|p_0-p_1|$ in both the public-key random-oracle game and the symmetric-cipher game, not the bit-guessing bias $|\Pr[\hat b=b]-1/2|$ for a uniformly hidden bit.

## Depends on

- [Variable-time trapdoor function scheme](../hardness-assumptions/variable-time-trapdoor-function-scheme.md)
- [One-wayness against efficient interactive adversaries](../hardness-assumptions/interactive-one-wayness.md)
- [Elementary wrappers](../../security-games/asymptotic-security/elementary-wrappers.md)
- [The random oracle model](the-random-oracle-model.md)
- [Distinguishing advantage](../../security-games/games-and-advantages/advantage.md)
- [Public-key encryption scheme](../../security-games/generic-security-games/pkescheme.md)
- [Private-key encryption scheme](../../security-games/generic-security-games/symm-enc-scheme.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 11.2
