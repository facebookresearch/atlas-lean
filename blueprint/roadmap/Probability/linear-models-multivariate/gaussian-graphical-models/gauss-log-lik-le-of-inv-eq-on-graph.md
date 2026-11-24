# Dempster's covariance-selection MLE

Let $G$ be a simple graph on a finite set $\iota$ and $S$ a real $\iota \times \iota$ matrix. Let $\hat K$ be a positive definite matrix [supported on](is-supported-on.md) $G$ whose inverse agrees with $S$ on the diagonal and on the edges: $(\hat K^{-1})_{ij} = S_{ij}$ whenever $i = j$ or $i \sim j$. Then $\hat K$ maximizes the [Gaussian log-likelihood](gauss-log-lik.md) $\log \det K - \operatorname{tr}(S K)$ over positive definite $K$ supported on $G$.

## Sources

- A. P. Dempster, *Covariance selection*, Biometrics 28 (1972), 157–175.
- S. L. Lauritzen, *Graphical Models*, Oxford University Press, 1996, Chapter 5.
