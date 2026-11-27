# Weak seed bank: Kingman coalescent with rates multiplied by 1/(E B)^2

In the $m$-step seed-bank model of Kaj, Krone and Lascoux with a fixed sample size $n\ge1$ and $N\ge n$ individuals per generation, each
individual has its parent $B$ generations earlier, chosen uniformly among the $N$ individuals there, with
$B$ independent and identically distributed with law $\mathbb P(B = j) = b_j$ on $\{1, \dots, m\}$, $m$ and
the $b_j$ not depending on $N$. Assume $\gcd \{ j : b_j > 0 \} = 1$. Let $A_N(k)$ be the number of
ancestors, $k$ generations back, of a sample of $n$ individuals of one generation, and
$\beta = 1/\mathbb E B$. Then $A_N(\lfloor N t \rfloor)$ converges weakly in the Skorokhod space
$D_{\{1, \dots, n\}}[0, \infty)$ to the pure death process started at $n$ that goes from $i$ to $i - 1$ at
rate $\beta^2 \binom i2$, the block-counting process of Kingman's coalescent run at rate $\beta^2$.

The case $B = 1$ is the Wright–Fisher model with $\beta = 1$. Without the gcd condition the averaging
fails: for $B = 2$ almost surely two lineages sampled in the same generation always go back to the same
generations, so a pair coalesces at rate $1/2$ instead of $\beta^2 = 1/4$.

## Depends on

- [Finite-N weak seed-bank ancestral chain with residual ages (bounded-support B)](finite-n-weak-seed-bank-ancestral-chain-with-res.md)

## Proof depends on

- [Mohle's separation-of-timescales lemma for finite Markov chains](../../../../Probability/markov-chains/finite-markov-chains/mohle-s-separation-of-timescales-lemma-for-finit.md)
- [Stationary averaging of the pair landing probability in the weak seed-bank model](stationary-averaging-of-the-pair-landing-probabi.md)

## Expansion

A sound expansion follows the source proof: write the one-step kernel of the configuration process
(numbers of ancestral lines by residual age) as $A + N^{-1} B + O(N^{-2})$, where $A$ moves only the
residual ages and $B$ carries the single coalescences; the separation-of-timescales lemma gives the limit
$P - I + e^{t P B P}$ with $P = \lim_k A^k$, which exists by the gcd condition; the stationary averaging
lemma identifies the averaged rate as $\beta^2 \binom i2$. The transition convergence is verified for every initial configuration of the fixed finite state space, uniformly over that space; the projected-semigroup convergence criterion used in the source then gives weak convergence of the count process. One-dimensional convergence from only the sampled initial state would not by itself suffice. The corresponding statement for the ancestral
partition, convergence of its finite-dimensional distributions to those of Kingman's coalescent at rate
$\beta^2$, needs in addition the exchangeability of the lineages and is not stated in the source.

## Sources

- I. Kaj, S. M. Krone and M. Lascoux, "Coalescent theory for seed bank models", Journal of Applied Probability 38 (2001), 285–300, <https://doi.org/10.1239/jap/996986745>; author preprint dated 22 September 2000, Theorem 1 (Section 2), Lemma 1, and Section 3, equations (9)–(17), using Lemma 1 of M. Möhle, "A convergence theorem for Markov chains arising in population genetics and the coalescent with selfing", Advances in Applied Probability 30 (1998), 493–512.
- J. Blath, A. González Casanova, N. Kurt and M. Wilke-Berenguer, "A new coalescent for seed-bank models", Annals of Applied Probability 26 (2016), 857–891, <https://doi.org/10.1214/15-AAP1106>, preprint <https://arxiv.org/abs/1411.4747>, Section 1 (summary of the result, the rate factor $\beta^2 = 1/(\mathbb E B)^2$).
