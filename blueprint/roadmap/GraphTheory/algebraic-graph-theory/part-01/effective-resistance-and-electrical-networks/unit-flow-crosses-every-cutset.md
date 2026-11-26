# A unit flow crosses every cutset

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed). If $P \subseteq E$ [separates](separating-edge-set.md) $a$ from $z$ and $\theta$ is a [unit flow](is-unit-flow.md) from $a$ to $z$, then

$$\sum_{e \in P} \lvert\theta_e\rvert \ge 1$$

(R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, proof of the Nash-Williams Inequality, Section 2.5, via flow conservation, Lemma 2.8).
