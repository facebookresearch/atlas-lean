# Low-degree conjecture

A **testing problem** is a sequence of pairs of distributions $(\mathbb{Q}_n, \mathbb{P}_n)$ on $\mathbb{R}^{N_n}$ (null and planted), with $\mathbb{P}_n \ll \mathbb{Q}_n$ and likelihood ratio $L_n = d\mathbb{P}_n/d\mathbb{Q}_n \in L^2(\mathbb{Q}_n)$. **Strong detection** means a test with $\mathbb{Q}_n(\text{reject}) + \mathbb{P}_n(\text{accept}) \to 0$; **weak detection** means this sum is at most $1 - \Omega(1)$. The **low-degree conjecture** (Hopkins) is the hypothesis that for sufficiently "natural" high-dimensional testing problems — in particular those whose null distribution is a product measure and whose planted distribution is invariant under permutations of coordinates and robust to small amounts of noise — if $\|L_n^{\le D}\| = O(1)$ for some $D = D(n) \ge (\log n)^{1+\delta}$, then no algorithm running in time $\exp(\tilde O(D))$ achieves strong detection. It is a conjecture, not a theorem: it is false without noise-robustness (for instance, planted problems solvable by Gaussian elimination over finite fields have small low-degree advantage), and its scope is delimited by these counterexamples. Under the conjecture, bounded low-degree advantage at degree $n^{\delta}$ predicts that subexponential time $\exp(n^{\delta - o(1)})$ is needed.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)

## Sources

- S. B. Hopkins, "Statistical Inference and the Sum of Squares Method", PhD thesis, Cornell University (2018).
- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
