# Leftover hash lemma with side information

Statement under preparation: the leftover hash lemma when the adversary also holds side information $z$ correlated with the source $s$: for a universal hash $H$ with uniformly random key $k$ independent of $(s, z)$, where $H$ maps into a set $T$ of size $N$ and is $(1+\alpha)/N$-universal, the statistical distance between $(k, z, H(k, s))$ and $(k, z, t)$ with $t$ uniform on $T$ is bounded in terms of $N$, the slack $\alpha$ and the conditional guessing probability of $s$ given $z$. Two forms are in use: a worst-case form with $\gamma_{\mathrm{wc}} = \max_z \max_x \Pr[s = x \mid z]$, the maximum over $z$ with $\Pr[z] > 0$, obtained by applying the unconditional lemma to each such $z$; and an average-case form with $\gamma_{\mathrm{avg}} = \mathbb{E}_z \max_x \Pr[s = x \mid z]$ (Dodis, Ostrovsky, Reyzin and Smith), obtained by averaging the per-$z$ bound and using concavity of the square root (Jensen's inequality).

Before this page is ready, it states the unconditional bound exactly as in the cited textbook, derives the worst-case form, and states the average-case form against the primary source.

## Depends on

- [Conditional guessing probability and min-entropy](../../randomness-extraction/conditional-guessing-probability-and-min-entropy.md)

## Proof depends on

- [Leftover hash lemma](../../randomness-extraction/leftover-hash-lemma.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>
- Y. Dodis, R. Ostrovsky, L. Reyzin and A. Smith, "Fuzzy extractors: how to generate strong keys from biometrics and other noisy data", *SIAM Journal on Computing* 38(1):97–139, 2008
