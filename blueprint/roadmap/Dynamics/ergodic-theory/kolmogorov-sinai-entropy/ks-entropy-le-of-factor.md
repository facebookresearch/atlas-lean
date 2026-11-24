# Entropy does not increase under factors

Let $(X, \mu)$ and $(Y, \nu)$ be probability spaces, $T : X \to X$ a map, $S : Y \to Y$ a measurable map, and
$\pi : X \to Y$ a measure-preserving map with $\pi \circ T = S \circ \pi$. Then

$$h_\nu(S) \le h_\mu(T):$$

every finite measurable partition of $Y$ [pulls back](preimage.md) to a measurable partition of $X$ with
[the same relative entropy](entropy-rel-preimage.md).

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), §4.3.1, Definition 4.3 (the inequality follows from the
  definition; the notes do not state it separately).
