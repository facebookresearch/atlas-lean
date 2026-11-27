# Group privacy along a chain

If $M$ is $\varepsilon$-differentially private and $z_0, z_1, \dots, z_k$ is a chain of databases in
which consecutive ones are neighbours, then for every measurable $S$,

$$
M(z_0)(S) \le e^{k \varepsilon} M(z_k)(S).
$$

Groups of $k$ individuals correspond to such chains: the guarantee degrades linearly in the size of
the group, which is what one wants, since replacing a whole population should change the answers.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Theorem 2.2.
