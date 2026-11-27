# An infinite VCL tree forces arbitrarily slow universal rates

If $H$ has an infinite VCL tree, then $H$ requires arbitrarily slow rates: for every $R : \mathbb{N} \to [0,1]$ with $R(n) \to 0$ and every learner there is a realizable distribution $P$ such that $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge R(n)$ for infinitely many $n$.

## Proof sketch

Along a random branch of the infinite VCL tree the level-$k$ tuple is shattered by concepts consistent with all earlier levels. Allocating probability mass $p_k$ to the $k+1$ points of level $k$ with $\sum_k p_k \le 1$ chosen so that $p_k$ decays as slowly as $R$ demands, a sample of size $n$ sees only a vanishing fraction of the points at the first unsaturated level, whose labels are fair coins given the sample. The resulting expected error is at least a constant times $p_k$ at the relevant level, which beats $R(n)$ infinitely often; a deterministic branch is extracted by Fatou's lemma.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [VCL trees and the VCL dimension](vcl-tree.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
