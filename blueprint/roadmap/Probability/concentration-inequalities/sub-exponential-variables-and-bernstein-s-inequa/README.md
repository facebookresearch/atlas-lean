# Sub-exponential variables and Bernstein's inequality

A real random variable is sub-exponential with parameters $(\nu, \alpha)$ when its moment
generating function satisfies $\mathbb{E}[e^{tX}] \le e^{\nu^2 t^2 / 2}$ for $|t| < 1/\alpha$, a
neighbourhood of $0$ rather than the whole line as for sub-Gaussian variables. Such variables
have a Gaussian tail for moderate deviations and an exponential tail for large ones. Bernstein's
inequality is the main example: a bounded centred variable with small variance $\sigma^2$
satisfies a tail bound of order $e^{-t^2 / (2(\sigma^2 + bt))}$, much sharper than Hoeffding's
bound when $\sigma^2 \ll b^2$. These are the first tools of non-asymptotic high-dimensional
statistics (Wainwright, *High-Dimensional Statistics*, 2019, Chapter 2).

- [Sub-exponential random variable](has-subexponential-mgf.md)
- [Sub-Gaussian variables are sub-exponential](has-subexponential-mgf-2.md)
- [Negation of a sub-exponential variable](neg.md)
- [Sub-exponential variables under an image measure](of-map.md)
- [Chernoff bound for a sub-exponential variable](measure-real-ge-le-exp.md)
- [Sub-exponential tail bound, Gaussian regime](measure-real-ge-le-of-le.md)
- [Sub-exponential tail bound, exponential regime](measure-real-ge-le-of-ge.md)
- [Sums of independent sub-exponential variables](sum-of-i-indep-fun.md)

## Bernstein's inequality

- [Exponential series bound for Bernstein's inequality](exp-le-one-add-add-sq-div-of-abs-lt-one.md)
- [Bernstein's bound on the moment generating function of a bounded variable](mgf-le-of-abs-le.md)
- [Bernstein's inequality for bounded variables, upper tail](measure-real-ge-le-bernstein.md)
- [Bernstein's inequality for bounded variables, two-sided](measure-real-abs-ge-le-bernstein.md)
- [Bernstein's moment generating function bound](mgf-le-of-bernstein-condition.md)
- [Bernstein's inequality under the Bernstein condition](measure-real-abs-ge-le-of-bernstein-cond.md)
- [Bernstein's inequality](bernstein-inequality.md)

## Chi-square and Gaussian concentration

- [A centred χ²₁ variable is sub-exponential with parameters (2, 4)](has-subexponential-mgf-sq-sub-one-gaussi.md)
- [Tail bound for the χ²ₙ distribution](measure-real-abs-chi-sq-mean-sub-one-ge.md)
- [Concentration of Lipschitz functions of Gaussian variables](lipschitz-concentration-std-gaussian.md)

## Related topics

- [Hoeffding's inequality](../hoeffding-s-inequality/README.md)
- [McDiarmid's inequality](../mcdiarmid-s-inequality/README.md)
- [Lasso error bounds under restricted eigenvalues](../../linear-models-multivariate/lasso-error-bounds-under-restricted-eigenvalues/README.md)
- [Generalization bounds and concentration](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/README.md)
