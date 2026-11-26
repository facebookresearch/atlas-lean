# Per-coordinate damped weight

Let $E$ be a finite set, $p$ and $u$ real numbers, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$, with [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) $\hat f(S)$. The per-coordinate damped weight of $e \in E$ is

$$D_e(u) = \sum_{S \subseteq E,\ e \in S} \big(\sqrt{1 - u}\big)^{2\lvert S \setminus \{e\}\rvert} \Big(\frac{\hat f(S)}{\sqrt{p(1-p)}}\Big)^2,$$

where $\sqrt{x} = 0$ for $x < 0$ and a quotient by $0$ is read as $0$. For $u \le 1$ the factor $\big(\sqrt{1-u}\big)^{2\lvert S \setminus \{e\}\rvert}$ is $(1 - u)^{\lvert S\rvert - 1}$.
