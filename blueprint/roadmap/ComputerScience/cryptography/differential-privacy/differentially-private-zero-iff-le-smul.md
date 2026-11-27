# Pure differential privacy as a measure inequality

A mechanism $M$ is $\varepsilon$-differentially private if and only if $M(x) \le e^{\varepsilon} M(y)$
as measures for all neighbours $x, y$. This form is what makes pure differential privacy pass
through integrals: $\int f \, dM(x) \le e^{\varepsilon} \int f \, dM(y)$ for every nonnegative
measurable $f$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 2.4 with $\delta = 0$; compare Remark 3.2 (Section 3.5.1, after Definition 3.6), where the same condition is $D_\infty(M(x) \| M(y)) \le \varepsilon$.
