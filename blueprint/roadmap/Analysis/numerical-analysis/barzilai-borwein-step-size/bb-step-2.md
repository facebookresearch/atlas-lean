# Second Barzilai–Borwein step size

For the step $s$ and the gradient change $y$, the second Barzilai–Borwein step size is

$$\alpha = \frac{s^\top y}{y^\top y},$$

which makes $\alpha I$ the [best scalar fit](norm-sub-bb-step-smul-le.md) of the inverse secant
equation $H y = s$.

## Sources

- W. Yin, UCLA Math 164 lecture notes *Barzilai–Borwein method* (2015); https://www.cmor-faculty.rice.edu/~yzhang/caam565/L1_reg/BB-step.pdf.
