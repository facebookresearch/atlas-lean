# Minimum description length bound

Let $\mathcal{H}$ be a countable hypothesis class with a prefix-free description language
$d : \mathcal{H} \to \{0,1\}^*$, write $|h|$ for the length of $d(h)$, and let the loss take values in
$[0,1]$. For every $m$ and $\delta \in (0,1)$, with probability at least $1-\delta$ over $S \sim
\mathcal{D}^m$, for all $h \in \mathcal{H}$,

$$L_\mathcal{D}(h) \le L_S(h) + \sqrt{\frac{|h| + \ln(2/\delta)}{2m}}.$$


## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: Finite classes: agnostic uniform convergence and PAC bound.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 7.7. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
