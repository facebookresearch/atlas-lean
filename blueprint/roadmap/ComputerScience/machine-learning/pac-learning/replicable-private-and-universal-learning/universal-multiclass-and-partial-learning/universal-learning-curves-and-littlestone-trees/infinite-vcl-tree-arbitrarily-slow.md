# An infinite VCL tree forces arbitrarily slow universal rates

If $H \subseteq \{0,1\}^X$ has an infinite VCL tree, then $H$ requires arbitrarily slow rates: for every rate function $R : \mathbb{N} \to [0,1]$ with $R(n) \to 0$ and every learner there is a realizable distribution $P$ such that

$$
\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge \frac{R(n)}{40} \quad \text{for infinitely many } n .
$$

## Proof sketch

From $R$ build probabilities $p_1, p_2, \dots$ with $\sum_k p_k = 1$ and increasing integers $n_i, k_i$ with $\sum_{k > k_i} p_k \le 1/n_i$, $n_i p_{k_i} \le k_i$ and $p_{k_i} = C R(n_i)$ for a constant $\tfrac12 \le C \le 1$. Choose a uniformly random branch of the infinite VCL tree and let $P_{\mathbf{y}}$ give the $k$ points of the depth-$(k-1)$ node on the branch mass $p_k / k$ each, labelled by the branch; every finite branch is realized, so $P_{\mathbf{y}}$ is realizable. At sample size $n_i$, a constant fraction of the $k_i$ points at level $k_i$ is unseen, and their labels are fair coins given the sample, which yields expected error of order $p_{k_i} \asymp R(n_i)$; Fatou's lemma then gives one branch for which this happens for infinitely many $i$.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [VCL trees and the VCL dimension](vcl-tree.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Theorem 5.11, Lemma 5.12 and the proof of Theorem 5.11.
