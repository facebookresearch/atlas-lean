# Union bound over a finite class (the Occam bound)

Let $H$ be a finite set of hypotheses with measurable disagreement sets, $D$ a probability
distribution on labelled examples, $m \in \mathbb{N}$ and $\varepsilon \in [0, \infty]$. Then, with $(1 - \varepsilon)_+ = \max(1 - \varepsilon, 0)$ and $0^0 = 1$,

$$D^m\{S : \text{the version space of } H \text{ at } S \text{ contains some } h \text{ with } \operatorname{error}_D(h) > \varepsilon\} \le |H|\,(1 - \varepsilon)_+^m ,$$

where the version space is the set of members of $H$ that agree with
every labelled example of $S$. The event is the union, over the "bad" hypotheses of $H$, of the
events that each agrees with the sample.

This is the realizable (noise-free) counterpart of the finite-class uniform deviation bound: it
needs no concentration inequality and its sample size grows like $\log |H| / \varepsilon$ instead of
$\log |H| / \varepsilon^2$.

## Background

- [Uniform deviation of the empirical risk over a finite class](../../generalization-bounds-and-concentration/measure-real-exists-abs-empirical-risk-s.md):
  the agnostic version of the same union-bound argument, where Hoeffding's inequality replaces the
  exact probability $(1 - \operatorname{error})^m$ and the rate in $\varepsilon$ is quadratic.

## Sources

- A. Blumer, A. Ehrenfeucht, D. Haussler and M. K. Warmuth, *Occam's razor*, Information Processing Letters 24 (1987), 377-380.
- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Section 2.3.1, equations (2.5)-(2.9) and the display after (2.9).
