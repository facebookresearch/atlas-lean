# Rewinding against a committed table

Consider a two-stage experiment in which a first stage outputs a state $s$, a second stage from $s$ outputs a run $r$, the run is accepted or rejected, and each run opens some positions $j \in \mathbb{N}$ to bits $b \in \{0,1\}$. Suppose that for every possible state $s$: every accepted run opens only positions below $M$, and for every fixed table $\pi : \mathbb{N} \to \{0,1\}$, the probability that a run from $s$ is accepted while every opening agrees with $\pi$ is at most $\varepsilon$. Let $\varepsilon_1$ be the one-run acceptance probability and $\delta$ the probability that two independent runs from a shared state both accept, with some position $j < M$ opened to $0$ by the first and to $1$ by the second. Then

$$
\varepsilon_1 \le \varepsilon + M\sqrt{\delta}.
$$

## Proof sketch

Fix $s$ and choose at each position the bit that accepted runs open more often, defining a table $\pi_s$. An accepted run disagreeing with $\pi_s$ opens some position $j$ to its less likely bit, an event of probability $\min(p_j(0), p_j(1)) \le \sqrt{p_j(0)p_j(1)}$, where $p_j(0)p_j(1)$ is at most the probability that two independent runs open $j$ to both bits. A union bound over $j < M$ and Jensen's inequality over $s$ give the claim.

## Sources

- B. Barak and O. Goldreich, "Universal Arguments and their Applications", 17th IEEE Conference on Computational Complexity (CCC 2002), and SIAM Journal on Computing 38(5), 2008.
