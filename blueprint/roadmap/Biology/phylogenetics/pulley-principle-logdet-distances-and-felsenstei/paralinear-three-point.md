# Additivity of the LogDet distance at a separating vertex

Let $p_i > 0$ for every $i$ and let $M, N$ be real square matrices with unit row sums and nonzero determinants. Then

$$d_{LD}\bigl(M^\top \operatorname{diag}(p) N\bigr) = d_{LD}\bigl(M^\top \operatorname{diag}(p)\bigr) + d_{LD}\bigl(\operatorname{diag}(p) N\bigr),$$

where $d_{LD}$ is the [LogDet distance](paralinear.md): for $Y \sim p$ and $X, Z$ conditionally independent given $Y$ with transition matrices $M, N$, $d(X, Z) = d(X, Y) + d(Y, Z)$ (Steel 1994; Lockhart et al. 1994; Lake 1994).

## Sources

- M. A. Steel, *Recovering a tree from the leaf colourations it generates under a Markov model*, Appl. Math. Lett. 7 (1994), 19–23.
- P. J. Lockhart, M. A. Steel, M. D. Hendy and D. Penny, *Recovering evolutionary trees under a more realistic model of sequence evolution*, Mol. Biol. Evol. 11 (1994), 605–612.
- J. A. Lake, *Reconstructing evolutionary trees from DNA and protein sequences: paralinear distances*, Proc. Natl. Acad. Sci. USA 91 (1994), 1455–1459.
