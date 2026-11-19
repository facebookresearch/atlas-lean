# First-step equations for hitting times

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with connected [underlying graph](../oriented-incidence-matrices/underlying-graph.md), and let $w : E \to (0, \infty)$ be conductances. For $z \in V$, a function $h : V \to \mathbb{R}$ solves the first-step equations of the hitting times of $z$ if $h(z) = 0$ and, for every $x \ne z$,

$$h(x) = 1 + \frac{N(x)}{\pi(x)}, \qquad N(x) = \sum_{e:\ e^- = x} w_e\, h(e^+) + \sum_{e:\ e^+ = x} w_e\, h(e^-),$$

where $\pi(x) = \sum_e w_e \big([e^- = x] + [e^+ = x]\big)$ is the [weighted degree](../../part-02/conductance-and-cheeger-s-inequality/weighted-degree.md) (a loop counts twice). On a loopless multigraph this is the linear system satisfied by the expected hitting times of $z$ for the network random walk, which crosses an edge with probability proportional to its conductance (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Sections 2.2 and 2.7).

With a loop it is the system of a different walk: the loop is counted at both ends of $\pi(x)$ and of $N(x)$, so it is taken with probability $2 w_e/\pi(x)$ instead of the source's $w_e/\pi(x)$. For an edge $01$ and a loop at $0$, with unit conductances, the unique solution for $z = 1$ has $h(0) = 3$, while the source's walk has $\mathbb{E}_0[\tau_1] = 2$. On a connected loopless multigraph the system has exactly one solution ([existence](exists-is-hitting-time-solution.md), [uniqueness](is-hitting-time-solution-unique.md)). On the path $0 - 1 - 2$ with unit conductances, $(4, 3, 0)$ and $(0, 3, 4)$ solve it for $z = 2$ and $z = 0$.
