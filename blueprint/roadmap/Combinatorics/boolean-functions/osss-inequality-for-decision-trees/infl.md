# Influence of a coordinate

For a finite set $E$, weights $\nu = (\nu_e)_{e \in E}$ with $\nu_e : \{0, 1\} \to \mathbb{R}$, $g : \{0, 1\}^E \to \mathbb{R}$ and $e \in E$, the influence of $e$ on $g$ is

$$\mathrm{Inf}_e(g) = \mathbb{E}_\nu\big\lvert g(\omega^{e \to 1}) - g(\omega^{e \to 0})\big\rvert,$$

with $\mathbb{E}_\nu$ the [expectation](expect.md) under the product weight $\nu$. For the indicator of an event and a product probability weight it is the [probability that $e$ is pivotal](infl-indicator-eq-pivotal.md). For $0/1$-valued functions under the uniform measure it is $4$ times the quarter-square influence $\mathbb{E}\big[\big((g(x) - g(x^{\oplus e}))/2\big)^2\big]$.
