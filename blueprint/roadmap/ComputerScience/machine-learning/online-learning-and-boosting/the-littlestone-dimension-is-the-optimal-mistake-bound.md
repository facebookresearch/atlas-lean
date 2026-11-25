# The Littlestone dimension is the optimal mistake bound

Let $\mathcal{H}$ be a nonempty class of binary classifiers. A mistake tree of finite depth $d$ is a
complete binary tree of depth $d$ whose internal nodes are labeled by instances; $\mathcal{H}$ shatters it
if every root-to-leaf path is realized by some $h \in \mathcal{H}$ that labels each node on the path by
the direction the path takes. The Littlestone dimension $\mathrm{Ldim}(\mathcal{H})$ is the largest finite
shattered depth if these depths are bounded, and $\infty$ otherwise. For comparisons of version spaces,
set $\mathrm{Ldim}(\emptyset)=-1$.

For every nonnegative integer $k\le\mathrm{Ldim}(\mathcal{H})$ and every deterministic online learner, there is
a length-$k$ sequence realizable by one hypothesis in $\mathcal{H}$ on which the learner makes $k$ mistakes.
If $d=\mathrm{Ldim}(\mathcal{H})<\infty$, the Standard Optimal Algorithm, which predicts the label whose
induced version space has the larger Littlestone dimension (with a fixed tie rule), makes at most $d$
mistakes on every realizable sequence. Thus $d=\infty$ means that no uniform finite mistake bound exists;
it does not assert that every learner has a single globally realizable infinite sequence with infinitely many mistakes.

Moreover $\mathrm{VCdim}(\mathcal{H}) \le \mathrm{Ldim}(\mathcal{H})$, and the gap can be infinite:
thresholds on $[0,1]$ have VC dimension $1$ and infinite Littlestone dimension.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Shattering and VC dimension.

## Depends on

- [Online classification protocol, mistakes and regret](online-classification-protocol-mistakes-and-regret.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Definitions 21.4–21.5, Lemmas 21.6–21.7, Corollary 21.8, §21.1.1 and Theorem 21.9. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
- S. Ben-David, D. Pál and S. Shalev-Shwartz, *Agnostic online learning*, COLT 2009, Definition 8 (including the empty-version-space convention) and §2. <https://www.cs.mcgill.ca/~colt2009/papers/032.pdf>
