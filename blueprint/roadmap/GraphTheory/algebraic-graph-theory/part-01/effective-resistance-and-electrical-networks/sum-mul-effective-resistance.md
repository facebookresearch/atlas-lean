# Foster's identity

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops, with connected [underlying graph](../oriented-incidence-matrices/underlying-graph.md) and with conductances $w : E \to (0, \infty)$, and let $n = \lvert V\rvert$. Then

$$\sum_{e \in E} w_e\, R_{\mathrm{eff}}(e^-, e^+) = n - 1,$$

where $R_{\mathrm{eff}}$ is the [effective resistance](effective-resistance.md). Spielman and Srivastava, *Graph sparsification by effective resistances*, SIAM J. Comput. 40 (2011), arXiv:0803.0929, Lemma 3(iii) and the identity $\sum_e w_e R_e = \operatorname{Tr}(\Pi) = n - 1$ in the proof of Theorem 1, obtain it by writing the numbers $w_e R_{\mathrm{eff}}(e)$ as the diagonal of the idempotent matrix $W^{1/2} B L^{+} B^{\mathsf T} W^{1/2}$, whose rank is that of the incidence matrix, $n - 1$.

In R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, this is Foster's theorem, Exercise 2.65: $\sum_{e \in E_{1/2}} i^e(e) = n - 1$, where $i^e(e) = c(e) R(e^- \leftrightarrow e^+)$ is the unit current across $e$ (Section 4.2). Read through Kirchhoff's effective resistance formula, it says that a weighted uniform spanning tree has $n - 1$ edges on average.

## Background

- [Kirchhoff's effective resistance formula](kirchhoff-effective-resistance-formula.md): each term $w_e R_{\mathrm{eff}}(e)$ is the probability that the weighted uniform spanning tree contains $e$.
