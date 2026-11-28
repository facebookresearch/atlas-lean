# Multiclass boosting with label-independent oracle complexity

There is an efficient multiclass boosting algorithm which, for every $\varepsilon, \delta > 0$ and every distribution $D$ over $X \times Y$, given a training sample $S \sim D^m$ with $m = \tilde O(m_0/(\gamma^3 \varepsilon))$ and oracle access to a learning rule $W$, makes $\tilde O(1/\gamma^3)$ calls to $W$ and outputs a predictor $\bar H : X \to Y$ such that, with probability at least $1-\delta$, if $W$ satisfies the empirical $\gamma$-BRG condition for $S$ then $\Pr_{(x,y) \sim D}[\bar H(x) \ne y] \le \varepsilon$. Neither bound depends on $|Y|$. In addition, a $\gamma$-weak PAC learner (accuracy at least $\gamma > 0$) yields a $(k-1)$-list PAC learner for the smallest integer $k$ with $1/k < \gamma$, and a $k$-list PAC learner yields, for every $\epsilon > 0$, a weak PAC learner with accuracy $(1-2\epsilon)/k$. Hence, if the smallest list size $k(H)$ for which $H$ is list PAC learnable is finite, and $\gamma(H)$ is the supremum of the $\gamma \in [0,1]$ for which $H$ is $\gamma$-weak PAC learnable (a supremum that need not be attained), then $k(H)\,\gamma(H) = 1$; the hypothesis $k(H) < \infty$ excludes the undefined product $\infty \cdot 0$; and a class of finite $k$-DS dimension $d$ is $k$-list PAC learnable with error $\tilde O\big((d^5 k^4 + \log(1/\delta))/m\big)$ by a proof through boosting.

## Proof sketch

The booster runs Hedge over the sample, calling the weak learner with the current list function; the weak hypotheses are aggregated into a shorter list of labels per point, since beating a uniform guess from the list certifies that the correct label is among the heavily voted labels. Recursing on the list size (removing at least one label per stage) ends with a single label per point. The analysis is a potential argument on the weights in which $|Y|$ never enters; generalization follows from a sample compression argument.

## Depends on

- [Multiclass weak learnability relative to random guessing on lists](multiclass-weak-learning-condition.md)
- [List PAC learners and list learnability](list-pac-learner.md)
- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Weak learnability implies PAC learnability via boosting](../../../../generalization-bounds-and-concentration/weak-learnability-implies-pac-learnability-via-boosting.md)
- [Generalization bound for sample compression schemes](../../../../generalization-bounds-and-concentration/generalization-bound-for-sample-compression-schemes.md)

## Sources

- N. Brukhim, A. Daniely, Y. Mansour, S. Moran, "Multiclass Boosting: Simple and Intuitive Weak Learning Criteria", NeurIPS (2023), arXiv:2307.00642, Theorems 1–3 and 5, Lemmas 2 and 3.
