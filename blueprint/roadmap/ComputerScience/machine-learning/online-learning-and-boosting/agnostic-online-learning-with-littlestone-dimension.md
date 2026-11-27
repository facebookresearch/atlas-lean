# Agnostic online learning with Littlestone dimension

Let $\mathcal{H}$ be a nonempty class of binary classifiers and write
$d = \mathrm{Ldim}(\mathcal{H}) \in \mathbb{N} \cup \{\infty\}$. For every positive integer horizon $T$,
if $d < \infty$ there is an online algorithm with predictions $p_t \in [0,1]$ such that for every sequence
$(x_1,y_1), \dots, (x_T,y_T)$ with binary labels,

$$\sum_{t=1}^T |p_t - y_t| - \min_{h \in \mathcal{H}} \sum_{t=1}^T |h(x_t) - y_t|
\le \sqrt{2 \min\{\log |\mathcal{H}|,\ d \log(eT)\}\, T}.$$

Here $\log |\mathcal{H}|$ means $+\infty$ when $\mathcal{H}$ is infinite. The minimum loss is attained even
for an infinite nonempty class, since its possible values belong to $\{0,\ldots,T\}$. The upper bound uses
weighted majority over the hypotheses when the class is finite, or over experts that simulate the Standard
Optimal Algorithm with chosen mistake times. When $d=0$, all hypotheses agree pointwise and zero regret is attainable.

Conversely, let $r=\min\{d,T\}$, with $\min\{\infty,T\}=T$. If $r\ge1$, every possibly randomized online
algorithm has some length-$T$ sequence on which its expected regret is
$\Omega(\sqrt{rT})$, with a universal implicit constant. Thus the $\Omega(\sqrt{dT})$ lower bound applies
when $1\le d\le T$; for $T<d$ or $d=\infty$ the lower bound is linear in $T$, not larger than the horizon.
The constant prediction $p_t=1/2$ always has regret at most $T/2$, including when $d=\infty$.

## Proof depends on

- [The Littlestone dimension is the optimal mistake bound](the-littlestone-dimension-is-the-optimal-mistake-bound.md)
- [The Hedge loss bound](hedge-algorithm/alg-loss-le.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 21.10 and its proof. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
- S. Ben-David, D. Pál and S. Shalev-Shwartz, *Agnostic online learning*, COLT 2009, Definition 8 and Lemma 14. The finite-horizon form above applies the lemma's block proof to a shattered tree of depth $\min\{d,T\}$, with block lengths differing by at most one. <https://www.cs.mcgill.ca/~colt2009/papers/032.pdf>
