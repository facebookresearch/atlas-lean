# Group privacy, approximate case

If $M$ is $(\varepsilon, \delta)$-differentially private with $\varepsilon \ge 0$, then along a chain of
$k$ neighbouring steps $M(z_0)(S) \le e^{k\varepsilon} M(z_k)(S) + k e^{(k-1)\varepsilon}\delta$: the
mechanism is $(k\varepsilon, k e^{(k-1)\varepsilon}\delta)$-differentially private for groups of size
$k$. The additive term "takes a big hit", unlike the pure case.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, footnote 1 to Theorem 2.2.
