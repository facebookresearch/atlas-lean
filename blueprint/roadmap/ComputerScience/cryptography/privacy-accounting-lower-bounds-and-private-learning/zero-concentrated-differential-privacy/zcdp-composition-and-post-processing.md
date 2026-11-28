# Adaptive composition and post-processing of zCDP

If $M_1$ is $\rho_1$-zCDP and, for every output $y$ of $M_1$, the mechanism $M_2(\cdot, y)$ is $\rho_2$-zCDP, then the adaptive composition $S \mapsto (M_1(S), M_2(S, M_1(S)))$ is $(\rho_1 + \rho_2)$-zCDP. If $M$ is $\rho$-zCDP and $g$ is any (randomized) function independent of the data, then $g \circ M$ is $\rho$-zCDP. Hence $k$ adaptively chosen Gaussian mechanisms with $\ell_2$-sensitivities $\Delta_j$ and noise levels $\sigma_j$ compose to $\sum_j \Delta_j^2/(2\sigma_j^2)$-zCDP.

## Proof sketch

Rényi divergence satisfies the chain rule $D_\alpha(P_{Y_1Y_2} \| Q_{Y_1Y_2}) \le D_\alpha(P_{Y_1} \| Q_{Y_1}) + \sup_y D_\alpha(P_{Y_2 \mid y} \| Q_{Y_2 \mid y})$, obtained by integrating out the second coordinate under the $\alpha$-power, and the data processing inequality for Markov kernels. Applying both at every order $\alpha$ preserves the linear-in-$\alpha$ form.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)

## Proof depends on

- [The Gaussian mechanism satisfies zCDP with parameter sensitivity squared over twice the variance](gaussian-mechanism-zcdp.md)
- [Post-processing, adaptive composition and conversion for Rényi differential privacy](../../renyi-differential-privacy/renyi-dp-composition-and-conversion.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Lemmas 1.7, 1.8 and 2.3.
