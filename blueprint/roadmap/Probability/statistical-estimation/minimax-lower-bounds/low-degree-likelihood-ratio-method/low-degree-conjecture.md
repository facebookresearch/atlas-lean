# Low-degree conjecture

A **testing problem** is a sequence of pairs of distributions $(\mathbb{Q}_n, \mathbb{P}_n)$ on $\mathbb{R}^{N_n}$ (null and planted), with $\mathbb{P}_n \ll \mathbb{Q}_n$ and likelihood ratio $L_n = d\mathbb{P}_n/d\mathbb{Q}_n \in L^2(\mathbb{Q}_n)$. **Strong detection** means a test with $\mathbb{Q}_n(\text{reject}) + \mathbb{P}_n(\text{accept}) \to 0$; **weak detection** means this sum is at most $1 - \Omega(1)$. The **low-degree conjecture** (Hopkins) is the hypothesis that for sufficiently "natural" high-dimensional testing problems (in particular those whose null distribution is a product measure and whose planted distribution is invariant under permutations of coordinates and robust to small amounts of noise), if $\|L_n^{\le D}\| = O(1)$ for some $\delta > 0$ and $D = D(n) \ge (\log n)^{1+\delta}$, then no polynomial-time algorithm achieves strong detection. Its more general form (Hopkins' Hypothesis 2.1.5) takes degree-$D$ polynomials as a proxy for algorithms running in time $n^{\tilde\Theta(D)}$, so bounded advantage at degree $D$ predicts that time $n^{\tilde\Omega(D)}$ is needed. It is a conjecture, not a theorem: it is false without noise-robustness (for instance, planted problems solvable by Gaussian elimination over finite fields have small low-degree advantage), and its scope is delimited by these counterexamples. Under the conjecture, bounded low-degree advantage at degree $n^{\delta}$ predicts that subexponential time $\exp(n^{\delta - o(1)})$ is needed.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)

## Sources

- S. B. Hopkins, "Statistical Inference and the Sum of Squares Method", PhD thesis, Cornell University (2018).
- S. B. Hopkins, P. K. Kothari, A. Potechin, P. Raghavendra, T. Schramm, D. Steurer, "The power of sum-of-squares for detecting hidden structures", FOCS (2017), arXiv:1710.05017.
- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
