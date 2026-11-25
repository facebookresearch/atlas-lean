# Group privacy along a chain, approximate case

If $M$ is $(\varepsilon, \delta)$-differentially private and $z_0, \dots, z_k$ is a chain of
neighbours, then for every measurable $S$,

$$
M(z_0)(S) \le e^{k\varepsilon} M(z_k)(S) + \Big(\sum_{i < k} e^{i\varepsilon}\Big)\delta ,
$$

by iterating the definition along the chain.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, footnote 1 to Theorem 2.2 (the approximation term grows along the chain).
