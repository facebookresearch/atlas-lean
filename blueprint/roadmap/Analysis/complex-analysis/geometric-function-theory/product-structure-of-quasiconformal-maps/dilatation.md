# Metric dilatation of a planar map

For $f : \mathbb{R}^2 \to \mathbb{R}^2$ and $x \in \mathbb{R}^2$, with $\mathbb{R}^2$ carrying the sup norm $\|(u, v)\| = \max(|u|, |v|)$, the metric dilatation of $f$ at $x$ is

$$
H_f(x) = \limsup_{r \to 0^+} \frac{\sup_{\|y - x\| = r} \|f(y) - f(x)\|}{\inf_{\|y - x\| = r} \|f(y) - f(x)\|},
$$

the upper limit, as $r$ decreases to $0$, of the ratio of the supremum to the infimum of the distances from $f(x)$ of the images of the points on the sup-norm sphere of radius $r$ about $x$ (the boundary of a square). For continuous $f$, in particular for homeomorphisms, these are the greatest and the least such distance, since the sphere is compact; for an arbitrary map they need not be attained. The value lies in $[0, \infty]$: distances are taken in $[0, \infty]$, and a positive number divided by $0$ is $\infty$, while $0/0 = 0$.

The sup norm gives the same class of quasiconformal maps as the Euclidean norm, since the two norms are comparable, but not the same numerical bounds on the dilatation.
