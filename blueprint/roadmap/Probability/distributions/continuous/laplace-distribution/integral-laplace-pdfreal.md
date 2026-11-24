# The Laplace density integrates to one

For $b > 0$ and every $m$, $\int_{\mathbb{R}} \exp(-|z - m| / b) / (2b) \, dz = 1$: translate to
$m = 0$, use the symmetry $z \mapsto |z|$ to reduce to $2 \int_0^\infty e^{-z/b} \, dz / (2b)$, and
$\int_0^\infty e^{-z/b} \, dz = b$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 3.2 (the density is normalised).
