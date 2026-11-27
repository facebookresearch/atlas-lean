# Damped influence of a coordinate

Let $E$ be a finite set, $p$ and $\rho$ real numbers, and $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^E$, with [$p$-biased Fourier coefficients](../../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/pbiased-tensorize/ptn-coeff.md) $\hat f(S)$. The damped influence of $e \in E$ is

$$D_e(\rho) = \sum_{S \subseteq E,\ e \in S} \rho^{2\lvert S \setminus \{e\}\rvert} \Big(\frac{\hat f(S)}{\sigma}\Big)^2, \qquad \sigma = \sqrt{p(1-p)},$$

where $\sqrt{x} = 0$ for $x < 0$ and a quotient by $\sigma = 0$ is read as $0$.
