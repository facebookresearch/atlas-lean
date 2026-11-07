# Conjugate rearrangements have the same graph

Let $d_0, \dots, d_k$ be natural numbers
and let $\pi_1, \pi_2, \tau_1, \tau_2$ be permutations of $\{0, \dots, k\}$ with
$\pi_1 \tau_1 \pi_1^{-1} = \pi_2 \tau_2 \pi_2^{-1}$. Then the graph of the digits
$d_{\pi_1(0)}, \dots, d_{\pi_1(k)}$ with digit permutation $\tau_1$ and the graph of the digits
$d_{\pi_2(0)}, \dots, d_{\pi_2(k)}$ with digit permutation $\tau_2$ have the same edge set:

$$\{(d_{\pi_1(j)}, d_{\pi_1(\tau_1(j))}) : 0 \le j \le k\} =
\{(d_{\pi_2(j)}, d_{\pi_2(\tau_2(j))}) : 0 \le j \le k\}.$$

The source assumes, for a base $b$ and a multiplier $n$ with $1 < n < b$, that
$(d_{\pi_1(k)}, \dots, d_{\pi_1(0)})_b$ is an $(n, b, \tau_1)$-permutiple and that
$(d_{\pi_2(k)}, \dots, d_{\pi_2(0)})_b$ is an $(n, b, \tau_2)$-permutiple, together with a base
permutiple $(d_k, \dots, d_0)_b$; these hypotheses are not needed.

## Sources

- B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025), Article A13, Theorem 4.
