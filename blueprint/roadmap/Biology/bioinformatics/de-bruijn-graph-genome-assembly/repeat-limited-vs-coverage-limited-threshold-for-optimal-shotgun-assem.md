# Repeat-limited versus coverage-limited threshold for shotgun assembly

Model a circular DNA sequence of length $G$ with i.i.d. letters of distribution $p = (p_1, \dots, p_4)$ on $\{A, C, G, T\}$, and $N$ noiseless reads of length $L$ with independent uniformly distributed starting locations; an assembly algorithm must reconstruct the sequence exactly, with error probability at most $\varepsilon$. Let $N_{\mathrm{cov}}(\varepsilon, G, L)$ be the number of reads needed to cover the sequence with probability $1 - \varepsilon$, which by the Lander–Waterman analysis satisfies $N_{\mathrm{cov}}/(G/\bar L) \to 1$, i.e. $N_{\mathrm{cov}} \sim (G/L)\ln G$, as $L, G \to \infty$ with $\bar L = L/\log G$ fixed (Lemma 3); let $N_{\min}(\varepsilon, G, L)$ be the minimum number of reads for reconstruction and $c_{\min}(\bar L) = \lim N_{\min}/N_{\mathrm{cov}}$ in the same limit. Motahari, Bresler and Tse (2013, Theorem 1) prove that for every fixed $\varepsilon < 1/2$, $c_{\min}(\bar L) = \infty$ if $\bar L < 2/H_2(p)$ and $c_{\min}(\bar L) = 1$ if $\bar L > 2/H_2(p)$, where $H_2(p) = -\log\sum_i p_i^2$ is the Rényi entropy of order $2$. Informally, below the threshold two pairs of interleaved repeats of length about $L$ occur with high probability and make reconstruction impossible; above it, a simple greedy algorithm succeeds once the sequence is covered. Their Theorem 6 gives the same dichotomy for a stationary ergodic Markov sequence with transition matrix $Q$, with $H_2(p)$ replaced by the Rényi entropy rate $H_2(Q) = \log(1/\rho_{\max}(\bar Q))$, where $\bar Q = [q_{ij}^2]$.

## Depends on

- [Lander–Waterman limit for the uncovered fraction](../lander-waterman-coverage-model/tendsto-normalized-count-uncovered.md)

## Expansion

1. The model, the perfect-reconstruction criterion and the asymptotic regime $L = \bar L\log G$.
2. Lemma 3: the coverage asymptotics by a coupon-collector argument.
3. The repeat lower bound (Section 2.2): the probability of identical substrings (Lemma 12) and interleaved repeats below $2/H_2(p)$.
4. The greedy algorithm and its success above the threshold once the sequence is covered (Section 2.3 and Appendix A).
5. Theorem 6: the Markov extension.

## Sources

- A. S. Motahari, G. Bresler and D. N. C. Tse, Information theory of DNA shotgun sequencing, IEEE Trans. Inform. Theory 59 (2013), 6273–6289; arXiv:1203.6233, Section 2.1, Lemma 3, Theorems 1 and 6. <https://arxiv.org/abs/1203.6233>
