# Generalization bound for sample compression schemes

Let $A$ be a learning rule given by a compression scheme of size $k$: for an integer $k \ge 1$, a compression map selects a sequence $I$ of $k$ indices of the sample $S$, and a reconstruction map outputs a hypothesis from $S_I$. Let the loss take values in $[0,1]$, let $m \ge 2k$ and $0 < \delta < 1$, and write $V$ for the examples of $S$ not indexed by $I$. With
probability at least $1 - \delta$ over $S \sim \mathcal{D}^m$,

$$L_\mathcal{D}(A(S)) \le L_V(A(S)) + \sqrt{L_V(A(S))\, \frac{4k \log(m/\delta)}{m}} + \frac{8k \log(m/\delta)}{m}.$$

In particular, if $L_V(A(S)) = 0$ then $L_\mathcal{D}(A(S)) \le 8k \log(m/\delta)/m$.

## Depends on

- [The 0-1 loss as an abstract loss](../pac-learning/risk-of-the-0-1-loss/zero-one-loss.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 30.2 and Corollary 30.3. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
