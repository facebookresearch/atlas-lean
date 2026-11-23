# Adaptive composition of approximate differential privacy, two mechanisms

Let $M_1$ be $(\varepsilon_1, \delta_1)$-differentially private with values in probability measures,
and let the second mechanism be a Markov kernel chosen after seeing the first output, such that for
each first output $\omega$ the mechanism $x \mapsto M_2(x)(\omega, \cdot)$ is
$(\varepsilon_2, \delta_2)$-differentially private. Then releasing both outputs is
$(\varepsilon_1 + \varepsilon_2, \delta_1 + \delta_2)$-differentially private.

Proof (Dwork and Roth prove the $k$-fold statement in their Appendix B by a different route): for an event $S$, the probability of its section is at most
$h(\omega) + \delta_2$ with $h(\omega) = \min\{1, e^{\varepsilon_2} M_2(y)(\omega, S_\omega)\}$;
since $h$ takes values in $[0, 1]$, the layer-cake form of the $(\varepsilon_1, \delta_1)$ bound gives
$\int h \, dM_1(x) \le e^{\varepsilon_1} \int h \, dM_1(y) + \delta_1$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Theorem 3.16 for $k = 2$ and Section 3.5 (adaptive composition).
