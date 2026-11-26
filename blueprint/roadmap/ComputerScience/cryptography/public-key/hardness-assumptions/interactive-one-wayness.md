# One-wayness of trapdoor functions against efficient interactive adversaries

Fix a trapdoor function scheme and a positive security parameter $\lambda$. The challenger draws the public system parameter $\Lambda$ and sends it to the adversary. It generates a matching pair $(pk,sk)$ conditional on $\Lambda$, draws $x$ uniformly from the domain, and sends $(pk,F(pk,x))$ to the adversary. The adversary wins exactly when its answer is $x$. Its advantage is the probability of winning, over setup, the joint key law, the conditional uniform draw and the adversary’s independent fair bits. The adversary does not receive $sk$. In Boneh–Shoup’s Definition 10.4 the spaces depend on $(\lambda,\Lambda)$; for public-key-indexed spaces the draw of $x$ is additionally conditional on $pk$.

The scheme is **one-way against efficient interactive adversaries** if this advantage is negligible in $\lambda$ for every such adversary. An adversary is one uniform machine, initially given the security parameter, whose state persists between invocations. There must be a polynomial time bound $t$ and a negligible function $\epsilon$ such that for every positive $\lambda$ and **every environment**, even a computationally unbounded one, the probability that its **total** running time through halting exceeds $t(\lambda)$ is at most $\epsilon(\lambda)$. Almost-sure halting in each environment is assumed separately. A bound only in the honest challenger’s environment, or on the number of oracle queries alone, is not this condition.

This is the one-way hypothesis in Boneh–Shoup’s Theorems 11.2 and 13.3. [One-wayness on a public transcript](is-transcript-one-way.md) tests the same answer against the same public data but gives the encoded tuple to the observer at once. Substituting that formulation requires a justification that preserves the success probability and the required running-time guarantee; it is not part of the definition above.

## Depends on

- [Variable-time trapdoor function scheme](variable-time-trapdoor-function-scheme.md)
- [Efficient interactive machines](../../security-games/asymptotic-security/efficient-interactive-machines.md)
- [Negligible advantage](../../security-games/asymptotic-security/negligible-adv.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, September 2017, §2.4.3, especially Definition 2.11 and footnote 3, pp. 32–33; §10.2, Game 10.2 and Definitions 10.3–10.4, pp. 396–398. <https://toc.cryptobook.us/>
