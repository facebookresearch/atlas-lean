# Asymptotic efficiency and adaptive estimation

Asymptotic efficiency compares estimators through their limit laws in locally asymptotically normal models. Hájek's convolution theorem says that the limit law of every regular estimator is the normal law $N(0, I^{-1})$ convolved with some other law, so $I^{-1}$ is the best attainable asymptotic variance; Le Cam's one-step estimators attain it. In a semiparametric model, with a Euclidean parameter of interest and an infinite-dimensional nuisance parameter, the bound is that of the hardest parametric submodel, and an estimator is adaptive when it attains the bound of the model in which the nuisance parameter is known. Bickel's 1980 Wald lectures ("On adaptive estimation", 1982) develop the conditions for adaptation; the semiparametric theory is the subject of Bickel, Klaassen, Ritov and Wellner, *Efficient and Adaptive Estimation for Semiparametric Models* (1993).

- [Hájek's convolution theorem](hajek-convolution.md)
- [Adaptive estimation of a centre of symmetry](exists-adaptive-location-estimator.md)

## Related topics

- [Fisher information and the Cramér–Rao bound](../fisher-information-and-the-cram-r-rao-bound/README.md): the finite-sample information bound, in one and several parameters.
- [Contiguity and Le Cam's lemmas](../contiguity-and-le-cam-s-lemmas/README.md): the tools behind local asymptotic normality and the convolution theorem.
- [Asymptotic normality of maximum likelihood](../asymptotic-normality-of-maximum-likelihood/README.md): an estimator that attains the bound in regular parametric models.
- [Local power of the likelihood-ratio test](../../hypothesis-testing/local-power-of-the-likelihood-ratio-test/README.md): local asymptotic normality of the log-likelihood ratio.
- [Minimax lower bounds](../minimax-lower-bounds/README.md): non-asymptotic lower bounds by two-point and testing arguments.
