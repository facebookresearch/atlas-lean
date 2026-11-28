# Second moment method: bounded likelihood ratio norm rules out detection

A **testing problem** is a sequence of pairs of distributions $(\mathbb{Q}_n, \mathbb{P}_n)$ on $\mathbb{R}^{N_n}$ (null and planted), with $\mathbb{P}_n \ll \mathbb{Q}_n$ and likelihood ratio $L_n = d\mathbb{P}_n/d\mathbb{Q}_n \in L^2(\mathbb{Q}_n)$. **Strong detection** means a test with $\mathbb{Q}_n(\text{reject}) + \mathbb{P}_n(\text{accept}) \to 0$; **weak detection** means this sum is at most $1 - \Omega(1)$. If $\|L_n\| = O(1)$, then strong detection is impossible, and $\mathbb{P}_n$ is contiguous to $\mathbb{Q}_n$. If $\|L_n\| \to 1$, then weak detection is impossible, since

$$
d_{\mathrm{TV}}(\mathbb{P}_n, \mathbb{Q}_n) \le \tfrac12\sqrt{\|L_n\|^2 - 1}.
$$

Moreover the optimal test is the likelihood ratio test (Neyman–Pearson). The **low-degree method** replaces $\|L_n\|$ by $\|L_n^{\le D}\|$ and interprets $\|L_n^{\le D}\| = O(1)$ for $D \approx \log^{1+\delta} n$ as evidence that no polynomial-time test achieves strong detection.

## Proof sketch

By Cauchy–Schwarz, $2 d_{\mathrm{TV}} = \mathbb{E}_{\mathbb{Q}}|L - 1| \le \sqrt{\mathbb{E}_{\mathbb{Q}}(L-1)^2} = \sqrt{\|L\|^2 - 1}$. If $\|L_n\|$ stays bounded, then for events $A_n$ with $\mathbb{Q}_n(A_n) \to 0$ we get $\mathbb{P}_n(A_n) = \mathbb{E}_{\mathbb{Q}}[L_n\mathbf{1}_{A_n}] \le \|L_n\|\sqrt{\mathbb{Q}_n(A_n)} \to 0$, which is contiguity and precludes strong detection.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)
- [Total variation distance between finite measures](../../../convergence-of-measures/total-variation-distance/total-variation-dist.md)
- [Contiguity of sequences of measures](../../contiguity-and-le-cam-s-lemmas/is-contiguous.md)

## Proof depends on

- [Le Cam's first lemma](../../contiguity-and-le-cam-s-lemmas/is-contiguous-with-density-exp.md)
- [Neyman–Pearson lemma](../../../hypothesis-testing/neyman-pearson-dominated-two-simple.md)

## Sources

- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
