# Privacy and tails of the geometric mechanism

Let $f$ be integer valued with sensitivity at most $\Delta \ge 1$ (an integer). Adding discrete Laplace noise of scale $\Delta/\varepsilon$ to $f$ is $(\varepsilon, 0)$-differentially private. For scale $1/\varepsilon$ the noise $Y$ has tails

$$
\Pr[Y \ge m] = \Pr[Y \le -m] = \frac{e^{-\varepsilon(m-1)}}{e^{\varepsilon} + 1} \qquad (m \ge 1),
$$

and shifting the noise by an integer $s$ changes every probability by a factor at most $e^{\varepsilon |s|}$.

## Proof sketch

The mass ratio at $z$ and $z + s$ is $\alpha^{|z| - |z+s|} \le \alpha^{-|s|}$ by the triangle inequality; tails are geometric series.

## Depends on

- [The discrete Laplace (two-sided geometric) distribution](discrete-laplace-distribution.md)
- [Differential privacy](../differential-privacy/differentially-private.md)
- [Laplace mechanism](../laplace-and-exponential-mechanisms/laplace-mechanism.md)

## Sources

- Arpita Ghosh, Tim Roughgarden and Mukund Sundararajan, "Universally Utility-Maximizing Privacy Mechanisms", SIAM Journal on Computing, 2012.
- Clément L. Canonne, Gautam Kamath and Thomas Steinke, "The Discrete Gaussian for Differential Privacy", Advances in Neural Information Processing Systems 33, 2020.
