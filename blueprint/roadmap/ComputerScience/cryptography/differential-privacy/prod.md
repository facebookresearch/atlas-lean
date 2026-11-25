# Composition of pure differential privacy

If $M_1$ is $\varepsilon_1$-differentially private and $M_2$ is $\varepsilon_2$-differentially private
(with $s$-finite output laws), then releasing both, with independent coins, $x \mapsto M_1(x) \otimes M_2(x)$,
is $(\varepsilon_1 + \varepsilon_2)$-differentially private.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Theorem 3.14.
