# Thomson's principle, Pythagorean form

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with conductances $w : E \to (0, \infty)$ and [Laplacian](../graph-laplacians-and-cheeger-s-inequality/laplacian.md) $L$. Let $s, t \in V$, let $v : V \to \mathbb{R}$ satisfy $L v = \delta_s - \delta_t$, let $i$ be the [current](current-of.md) of $v$, and let $\theta$ be a [unit flow](is-unit-flow.md) from $s$ to $t$. Then

$$\mathcal{E}(\theta) = \big(v(s) - v(t)\big) + \mathcal{E}(\theta - i), \qquad \mathcal{E}(\eta) = \sum_{e \in E} \frac{\eta_e^2}{w_e}.$$

This is the orthogonal decomposition $\lVert\theta\rVert_r^2 = \lVert i\rVert_r^2 + \lVert\theta - i\rVert_r^2$ of R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, equation (2.10), together with $\mathcal{E}(i) = v(s) - v(t)$ from equation (2.7). The source states (2.10) for any flow between vertex sets $A$ and $Z$ with the same divergence as the current; here $A = \{s\}$, $Z = \{t\}$ and the strength is $1$, and no looplessness or connectivity hypothesis is needed.
