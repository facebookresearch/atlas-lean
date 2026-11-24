# Poisson-binomial mass function

For $m \in \mathbb{N}$, a vector $p = (p_0, \dots, p_{m-1}) \in \mathbb{R}^m$ and $j \in \mathbb{N}$, the
Poisson-binomial mass function is

$$\pi_p(j) = \sum_{\substack{A \subseteq \{0, \dots, m-1\} \\ |A| = j}} \prod_{i \in A} p_i \prod_{i \notin A} (1 - p_i) .$$

When every $p_i \in [0, 1]$, it is the law of the number of successes among $m$ independent trials
with success probabilities $p_i$; the algebraic identities about it hold for all real $p$.
