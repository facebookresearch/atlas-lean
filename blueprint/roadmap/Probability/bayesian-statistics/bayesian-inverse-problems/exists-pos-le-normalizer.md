# The normalising constants are uniformly positive on bounded data sets

Let the unknown $u$ live in a finite-dimensional real normed space $E$ with its Borel σ-algebra and prior probability measure $\mu_0$, let the data $y$ live in a seminormed group, let $r \ge 0$, and let the potential $\Phi(u; y)$ be continuous in $u$ and satisfy, for all $u$ and all $\|y\|, \|y'\| \le r$,

$$
\Phi(u; y) \ge -M_1(\|u\|), \qquad |\Phi(u; y) - \Phi(u; y')| \le M_2(\|u\|) \, \|y - y'\|,
$$

with $M_2$ nondecreasing and $\exp(M_1(\|u\|))$ integrable under $\mu_0$ (Theorem 4.3's condition; the
well-posedness theorem needs the stronger $\exp(M_1)(1 + M_2^2) \in L^1$). Then there is $z > 0$ with
$z \le Z(y)$ for every $\|y\| \le r$. The hypotheses also make $\exp(-\Phi(\cdot\,; y))$ integrable, so
each posterior is then a [probability measure](is-probability-measure-posterior.md).

This is Theorem 4.3 of Dashti and Stuart in the case $X' = X$ finite-dimensional, where the uniform
bound comes from a compact ball of positive prior mass on which $\Phi(\cdot\,; 0)$ is bounded.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Assumptions 4.2 and Theorem 4.3.
