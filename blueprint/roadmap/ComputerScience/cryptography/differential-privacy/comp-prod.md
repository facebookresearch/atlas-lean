# Adaptive composition of pure differential privacy

Let $M_1$ be $\varepsilon_1$-differentially private, and let the second mechanism be chosen after
seeing the first output $\omega$: a kernel $M_2(x)(\omega, \cdot)$ such that for each $\omega$ the
mechanism $x \mapsto M_2(x)(\omega, \cdot)$ is $\varepsilon_2$-differentially private. Assume that
every measure $M_1(x)$ is $s$-finite and every kernel $M_2(x)$ is $s$-finite. Then releasing
both outputs, $x \mapsto M_1(x) \otimes M_2(x)$, is $(\varepsilon_1 + \varepsilon_2)$-differentially
private. In measure form: $M_1(x) \le e^{\varepsilon_1} M_1(y)$ and
$M_2(x)(\omega, \cdot) \le e^{\varepsilon_2} M_2(y)(\omega, \cdot)$ integrate to
$M_1(x) \otimes M_2(x) \le e^{\varepsilon_1 + \varepsilon_2} M_1(y) \otimes M_2(y)$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Theorem 3.14 (stated for independent mechanisms) and Section 3.5 (composition with adaptively chosen mechanisms).
