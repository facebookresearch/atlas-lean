# Joint law of a hidden Markov model on paths and observation strings

Let $h$ be a hidden Markov model with finite state set $S$, finite observation set $O$ and real weights: initial weights $\pi(s)$, transition weights $a(s, s')$ and emission weights $b(s, o)$. A finite observation string $v = (v_0, \dots, v_t)$ is extended to a stream by $\bar v_i = v_i$ for $i \le t$ and $\bar v_i = v_0$ for $i > t$. For $t \in \mathbb{N}$, the joint law assigns to a pair of a state path $z = (z_0, \dots, z_t)$ and an observation string $v = (v_0, \dots, v_t)$ the path weight

$$P(z, v) = \pi(z_0)\, b(z_0, v_0) \prod_{k=1}^{t} a(z_{k-1}, z_k)\, b(z_k, v_k) .$$

## Sources

D. Jurafsky and J. H. Martin, *Speech and Language Processing*, 3rd ed. draft, Appendix A, Section A.2, eq. (A.8).
