# Volume factor from the determinant ratio

For $n \ge 2$,

$$
\sqrt{\Bigl(\frac{n^2}{n^2-1}\Bigr)^{n} \frac{n-1}{n+1}} = \frac{n}{n+1}\Bigl(\frac{n^2}{n^2-1}\Bigr)^{(n-1)/2} = \rho_n ,
$$

so the square root of the determinant ratio $\det A'/\det A$ computed in [the determinant after a step](det-next-matrix.md) is the [volume factor](volume-ratio.md). Together with the [volume formula](volume-ellipsoid.md) $\mathrm{vol}\, E(a, A) = \sqrt{\det A}\, \mathrm{vol}\, E(0, I)$ this gives the [exact volume factor](volume-next-ellipsoid.md) $\mathrm{vol}\, E(a', A') = \rho_n\, \mathrm{vol}\, E(a, A)$.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, proof of Lemma 7.1.
