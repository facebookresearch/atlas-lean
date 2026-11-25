# Finite-sample bound for the 1-nearest-neighbor rule

Let $d,m \ge 1$ be integers, let $\mathcal{X}=[0,1]^d$ have the Euclidean metric and its Borel sigma-algebra,
and let $\mathcal{Y}=\{0,1\}$. Let $\mathcal{D}$ be a probability distribution on $\mathcal{X}\times\mathcal{Y}$
admitting a version $\eta : \mathcal{X}\to[0,1]$ of $\Pr[Y=1\mid X=x]$ that is $c$-Lipschitz for some $c>0$.
For an independent sample $S=((x_1,y_1),\ldots,(x_m,y_m))\sim\mathcal{D}^m$, let $j_S(x)$ be the least index
minimizing $\|x-x_j\|_2$, and set $h_S(x)=y_{j_S(x)}$. In particular, distance ties are resolved independently
of the sample labels. Write $L_{\mathcal{D}}(h)=\Pr_{(X,Y)\sim\mathcal{D}}[h(X)\ne Y]$ and
$h^*(x)=\mathbb{1}[\eta(x)>1/2]$ for a Bayes optimal classifier. Then

$$\mathbb{E}_S[L_\mathcal{D}(h_S)] \le 2L_\mathcal{D}(h^*)+4c\sqrt{d}\,m^{-1/(d+1)}.$$


## Proof depends on

- [The Bayes classifier is optimal](../supervised-learning/bayes-classifier/is-bayes-estimator.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), §§19.1–19.2, Lemma 19.1, Lemma 19.2 and Theorem 19.3 (with the least-index distance-tie convention specified here). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
