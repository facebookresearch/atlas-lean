# Entropy does not increase under factors (almost-everywhere form)

Let $(X, \mu)$ and $(Y, \nu)$ be probability spaces, $T : X \to X$ a quasi-measure-preserving map ($T$ is
measurable and $\mu(T^{-1} A) = 0$ whenever $\mu(A) = 0$), $S : Y \to Y$ a measurable map, and $\pi : X \to Y$ a
measure-preserving map with $\pi \circ T = S \circ \pi$ $\mu$-almost everywhere. Then

$$h_\nu(S) \le h_\mu(T).$$

Every finite measurable partition of $Y$ [pulls back](preimage.md) to a measurable partition of $X$ with
[the same relative entropy](entropy-rel-preimage-of-ae.md).
