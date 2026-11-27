# Classes with no infinite VCL tree are learnable at linear rate

If $H$ has no infinite VCL tree, then $H$ is learnable at rate $1/n$: there is a learner such that for every realizable $P$ there are $C, c > 0$ with $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \le \dfrac{C}{cn}$ for all $n$.

## Proof sketch

The absence of an infinite VCL tree makes a second Gale–Stewart game, in which the adversary tries to keep presenting tuples of growing length that are shattered along the play, a win for the learner. Its winning strategy yields, from data, a pattern-avoidance function: after finitely many steps the learner can name, for each $k$-tuple, a labelling that the target never produces, so the target lies in a data-dependent class of finite VC dimension. Applying a one-inclusion-graph learner for that class to a fresh portion of the sample gives expected error $O(d/n)$ with a data-dependent but almost surely finite $d$, which is the linear rate.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [VCL trees and the VCL dimension](vcl-tree.md)

## Proof depends on

- [Open Gale–Stewart games are determined](gale-stewart-determinacy.md)
- [Optimal sample complexity of realizable PAC learning](../../../optimal-sample-complexity-of-realizable-pac-learning.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
