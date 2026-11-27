# Derivative of the ERGM score

Let $V$ be a finite vertex set, $t(G) \in \mathbb R^\iota$ statistics of graphs on $V$ with $\iota$ finite, and $P_\theta(G) \propto \exp(\theta \cdot t(G))$ the exponential random graph law. For an observed graph $y$, the score is $s(\theta) = t(y) - \mathbb E_\theta\, t$. For every direction $v$ and component $j$,

$$\frac{d}{ds}\Big|_{s=0} s_j(\theta + s v) = -\sum_k \Sigma_{jk}(\theta)\,v_k,$$

where $\Sigma(\theta)$ is the covariance matrix of $t$ under $P_\theta$.
