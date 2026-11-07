# Least squares, ridge and lasso regression

- [Residual sum of squares](rss.md)
- [Expansion of the residual sum of squares](rss-add.md)
- [Pythagoras for least squares](rss-eq-of-normal.md)
- [Least squares and the normal equations](rss-le-iff-normal.md)
- [Least-squares estimates exist](exists-normal.md)
- [Closed-form solution of the normal equations](normal-inv.md)
- [Convexity of the residual sum of squares](convex-on-rss.md)

## Gaussian noise: least squares is maximum likelihood

- [Gaussian likelihood of linear regression](gauss-likelihood.md)
- [The Gaussian likelihood decreases with the residual sum of squares](gauss-likelihood-le-iff.md)
- [Least squares is maximum likelihood](is-max-on-gauss-likelihood-iff.md)
- [Existence of the Gaussian maximum likelihood estimate](exists-is-max-on-gauss-likelihood.md)

## Ridge regression: MAP under a Gaussian prior

- [Ridge objective](ridge.md)
- [Expansion of the ridge objective around a solution of its normal equations](ridge-eq-of-normal.md)
- [Solutions of the ridge normal equations minimize the ridge objective](ridge-le-of-normal.md)
- [The ridge matrix is positive definite](pos-def-ridge.md)
- [Ridge estimate](ridge-estimate.md)
- [Closed form of ridge regression](ridge-le-ridge-estimate.md)
- [Density of independent centred Gaussian coordinates](prod-gaussian-pdfreal-zero.md)
- [Posterior kernel of ridge regression](ridge-posterior.md)
- [Ridge regression is MAP estimation](ridge-posterior-le-iff.md)
- [The ridge estimate maximizes the ridge posterior](is-max-on-ridge-posterior.md)

## Lasso: MAP under a Laplace prior

- [Lasso objective](lasso.md)
- [Laplace density](laplace-pdf.md)
- [Lasso posterior kernel](lasso-posterior.md)
- [Lasso is MAP estimation](lasso-posterior-le-iff.md)
- [Convexity of the lasso objective](convex-on-lasso.md)
- [Soft thresholding](soft-threshold.md)
- [Soft thresholding solves the one-dimensional lasso](soft-threshold-le.md)
- [Lasso with an orthonormal design](lasso-soft-threshold-le.md)
