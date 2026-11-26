# Student's $t$ law

For $k \in \mathbb{N}$, Student's $t$ law with $k$ degrees of freedom is the measure on $\mathbb{R}$ with Lebesgue density

$$f_k(t) = \frac{\Gamma\big(\frac{k+1}{2}\big)}{\sqrt{k\pi}\,\Gamma\big(\frac k2\big)} \Big(1 + \frac{t^2}{k}\Big)^{-(k+1)/2}.$$

For $k \ge 1$ it is a probability measure, and it is the law of $Z/\sqrt{V/k}$ for independent $Z \sim N(0, 1)$ and $V \sim \chi^2_k$ ([Student's $t$ law as a ratio](map-div-sqrt-chi-square-eq-student-t.md)). For $k = 0$ the density vanishes (with the conventions $\Gamma(0) = 0$ and division by zero equal to $0$), so the measure is the zero measure and is not the law of any random variable.

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, Definition 5.3.4.
