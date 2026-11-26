# Likelihood is the marginal of the joint law

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. A finite observation string $v = (v_0, \dots, v_t)$ is extended to a stream by $\bar v_i = v_i$ for $i \le t$ and $\bar v_i = v_0$ for $i > t$. For every $t \in \mathbb{N}$ and observation string $v = (v_0, \dots, v_t)$, the likelihood of $v_0, \dots, v_t$ (the sum over all state paths of the path weights on the stream $\bar v$) is the marginal of the joint law:

$$\mathcal{L}_t(\bar v) = \sum_{z \in S^{t+1}} P(z, v) .$$

No normalization is assumed.

## Sources

D. Jurafsky and J. H. Martin, *Speech and Language Processing*, 3rd ed. draft, Appendix A, Section A.2, eq. (A.10).
