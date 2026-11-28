# Unique endemic equilibrium of the network SIS model with media coverage

**Setting.** The [heterogeneous mean-field SIS model with media coverage](heterogeneous-mean-field-sis-model-with-media-coverage.md), with degree classes $k = 1, \dots, n$, edge-infection probability $\Theta$, prevalence $i = \sum_k p(k) i_k$ and threshold $R_0$.

**Theorem.** If $R_0 > 1$ the model has exactly one endemic equilibrium $E^* = (i_1^*, \dots, i_n^*, M^*)$; if $R_0 \le 1$ it has none. At $E^*$,

$$M^* = \frac{m_0 + \omega N i^*}{\lambda}, \qquad i_k^* = \frac{a\beta\lambda k\Theta}{a\beta\lambda k\Theta + \mu(a\lambda + k m_0) + \mu k \omega N i^*},$$

and $\Theta \in \big(0,\ 1 - \mu m_0/(a\beta\lambda)\big)$ is the unique positive root of the self-consistency equation $\Theta = G(\Theta)$ obtained by substituting $i_k^*$ (with $i^*$ expressed through $\Theta$) into $\Theta = \langle k\rangle^{-1}\sum_k k p(k) i_k^*$.

## Depends on

- [Heterogeneous mean-field SIS model with media coverage](heterogeneous-mean-field-sis-model-with-media-coverage.md)

## Expansion

Setting $i_k' = 0$ gives $a\beta k(1 - i_k^*)\Theta = \mu i_k^*(a + k M^*)$, and $M' = 0$ gives $M^*$; solving for $i_k^*$ yields the displayed formula. Multiplying the stationary equations by $p(k)$, summing and eliminating $M^*$ expresses $i^*$ as an explicit function of $\Theta$ that is positive only for $\Theta < 1 - \mu m_0/(a\beta\lambda)$ (an interval that is nonempty when $R_0 > 1$, since $R_0 < a\beta\lambda/(\mu m_0)$). The resulting map $G$ satisfies $G(0) = 0$, $G' > 0$ and $G'' < 0$ on that interval, and $G'(0) = R_0$: for small $\Theta$, $i_k^* \approx a\beta\lambda k\Theta/(\mu(a\lambda + k m_0))$, so $G(\Theta) \approx R_0\Theta$. An increasing strictly concave map through the origin has a positive fixed point exactly when its slope at $0$ exceeds $1$, and then only one. In the continuum Barabási–Albert case $p(k) = 2m^2 k^{-3}$ without media, the self-consistency equation can be integrated and gives the prevalence $i \sim 2 e^{-\mu/(m\beta)}$ as $\beta \to 0$, positive for every $\beta > 0$.

## Sources

- Y. Wang, J. Cao, Z. Jin, H. Zhang, G.-Q. Sun, "Impact of media coverage on epidemic spreading in complex networks", *Physica A* 392(23) (2013) 5824–5835, Section 3.2, Eqs. (5)–(12), Theorem 3 and Remark 3. <https://doi.org/10.1016/j.physa.2013.07.067> (PMC7185856).
