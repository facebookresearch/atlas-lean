# Neighbour sum of the network walk

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed). For conductances $w : E \to \mathbb{R}$, a function $h : V \to \mathbb{R}$ and $x \in V$, the neighbour sum is

$$N(x) = \sum_{e:\ e^- = x} w_e\, h(e^+) + \sum_{e:\ e^+ = x} w_e\, h(e^-),$$

the sum of $w_e\, h(\text{other end of } e)$ over the edges at $x$. In a loopless multigraph with positive conductances it is $\pi(x)$ times the expected value of $h$ after one step from $x$ of the network random walk, which moves along an edge chosen with probability proportional to its conductance (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 2.2). A loop at $x$ is counted at both of its ends, contributing $2 w_e h(x)$.
