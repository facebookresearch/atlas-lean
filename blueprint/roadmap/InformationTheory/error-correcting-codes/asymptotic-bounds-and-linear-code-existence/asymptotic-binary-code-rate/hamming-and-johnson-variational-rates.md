# Hamming and Johnson variational rates

Let $h$ be the binary entropy and fix $0<\delta<1/2$. The Hamming rate $V_H$ is the infimum of $h(a)-h(b)$ over $0\le b<a\le1/2$ satisfying

$$1-2\delta<\frac{2(a-b)(1-a-b)}{\sqrt{a(1-a)}}.$$

For the Johnson rate $V_J$, use real $(\alpha,\beta,\gamma,u)$ satisfying

$$
 \delta/2<\alpha<1/2,\quad 0\le\beta<\alpha/2,\quad
 0\le\gamma<(1-\alpha)/2,\quad
 \beta+\gamma<u<\min(\alpha,\alpha-\beta+\gamma,1-\alpha+\beta-\gamma).
$$

Put $z=1-2u$, $m=1-2\alpha$, $\sigma=1-2\beta-2\gamma$, and $\eta=1-2\alpha+2\beta-2\gamma$. Impose the additional strict inequality

$$1-\frac{\delta}{2\alpha(1-\alpha)}<
\frac{(\sigma\eta-mz^2)^2}{z^2(1-m^2)(1-z^2)}+
\frac{(z^2-\eta^2)(\sigma^2-z^2)}{z^2(1-m^2)\sqrt{1-z^2}}.$$

The infimum defining $V_J$ is of $1-h(\alpha)+h(u)-\alpha h(\beta/\alpha)-(1-\alpha)h(\gamma/(1-\alpha))$ over these tuples. Define $V(\delta)=\min(V_H,V_J)$.

## Depends on

- [Asymptotic binary code rate and the classical first bound](asymptotic-binary-code-rate.md)

## Implementation notes

Verify nonempty bounded objective sets on the intended interval, positivity of every divisor, and that strict spectral feasibility matches the stated finite Hamming and Johnson spectral models before using the infima.

## Sources

- [Pinned variational objectives and feasibility](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_BinaryCodes.lean#L55-L152)
