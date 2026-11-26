# The spike-triggered average recovers the filter for spherically symmetric stimuli

Let a linear–nonlinear neuron fire with probability $N(w\cdot s)$ given a stimulus $s \in \mathbb{R}^d$, where $N : \mathbb{R} \to [0, 1]$ is measurable, so that $N(w\cdot s)$ is a spike probability, and $w \ne 0$, and let the stimulus distribution be radially symmetric about the origin (stimuli of equal length are equally probable), with $E|s| < \infty$ and $E[N(w\cdot s)] > 0$. Chichilnisky (2001) shows that the spike-triggered average is then proportional to $w$: pairing each stimulus $s$ with its mirror image $s^*$ about the line through $w$, which has the same probability and the same projection $w\cdot s^* = w\cdot s$, makes $s + s^*$ proportional to $w$. Writing the constant explicitly,

$$E[s \mid \text{spike}] = \frac{E[s\, N(w\cdot s)]}{E[N(w\cdot s)]} = \kappa\, w, \qquad \kappa = \frac{E[(w\cdot s)\, N(w\cdot s)]}{|w|^2\, E[N(w\cdot s)]},$$

which follows by taking the inner product with $w$. So the spike-triggered average recovers the linear filter up to scale (this is the population identity behind the [consistency of the spike-triggered average](../consistency-of-the-spike-triggered-average/tendsto-spike-triggered-average.md)) whenever $\kappa \ne 0$; if $\kappa = 0$, for example for an even nonlinearity $N(-x) = N(x)$, it is $0$ and carries no information about $w$.

## Expansion

1. The model: the LN neuron, the spike probability, and radial symmetry of the stimulus law.
2. Decomposition $s = \frac{w\cdot s}{|w|^2} w + s_\perp$ and the vanishing of $E[s_\perp N(w\cdot s)]$ by the reflection $s_\perp \mapsto -s_\perp$, which preserves the law and fixes $w\cdot s$.
3. The formula for $\kappa$ and the degenerate case $\kappa = 0$.
4. The extension to elliptically symmetric stimuli after whitening, and the [consistency and convergence rates of the estimator](paninski-consistency-and-convergence-rates-of-spike-triggered-average.md), as separate statements.

## Sources

- E. J. Chichilnisky, A simple white noise analysis of neuronal light responses, Network: Comput. Neural Syst. 12 (2001), 199–213, equation (1) and the derivation that follows. <https://doi.org/10.1080/713663221>
