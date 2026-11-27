# Student's $t$ law as a ratio

Let $(\Omega, P)$ be a probability space, $k \ge 1$, and $Z, V : \Omega \to \mathbb{R}$ independent random variables with $Z \sim N(0, 1)$ and $V \sim \chi^2_k$. Then $Z/\sqrt{V/k}$ has the [Student $t$ law](student-tmeasure.md) with $k$ degrees of freedom, with density

$$\frac{\Gamma\big(\frac{k+1}{2}\big)}{\sqrt{k\pi}\,\Gamma\big(\frac k2\big)} \Big(1 + \frac{t^2}{k}\Big)^{-(k+1)/2}.$$

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, Definition 5.3.4.
