# Cross-entropy is entropy plus divergence

For probability mass functions $p$ and $q$ on a
finite alphabet, the cross-entropy $H(p, q)$ in bits equals $H(p) + D(p \parallel q) / \ln 2$,
where $H(p)$ is the Shannon entropy of $p$ in bits and $D(p \parallel q)$ is the
Kullback–Leibler divergence of $p$ from $q$ with the natural logarithm. The identity holds in
$[0, \infty]$ with no support hypothesis: when $p$ charges an outcome that $q$ rules out, both
sides are $\infty$.
