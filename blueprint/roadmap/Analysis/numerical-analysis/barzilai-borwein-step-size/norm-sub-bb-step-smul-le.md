# The second Barzilai–Borwein step is a least-squares secant fit

For all vectors $s, y$ and every real $t$,

$$\Bigl\| s - \frac{s^\top y}{y^\top y}\, y \Bigr\| \le \| s - t y \|:$$

the [second Barzilai–Borwein step](bb-step-2.md) $\alpha = s^\top y / y^\top y$ makes $\alpha I$ the
best scalar fit of the inverse secant equation $H y = s$.

## Sources

- W. Yin, UCLA Math 164 lecture notes *Barzilai–Borwein method* (2015); https://www.cmor-faculty.rice.edu/~yzhang/caam565/L1_reg/BB-step.pdf.
