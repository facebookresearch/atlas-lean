# Natarajan, DS and graph dimensions compared

For every class $C$ of functions $X \to \beta$,

$$
\mathrm{Ndim}(C) \le \mathrm{DSdim}(C) \le \mathrm{Gdim}(C),
$$

where $\mathrm{Ndim}$ is the Natarajan dimension and $\mathrm{DSdim}$ the Daniely-Shalev-Shwartz dimension (largest set on which the restriction of $C$ contains a pseudo-cube). If $\beta$ is finite with $k$ labels, then (Ben-David, Cesa-Bianchi, Haussler and Long) every finite G-shattered set has at most $4\,\mathrm{Ndim}(C)\,(\lfloor \log_2 k \rfloor + 2)$ points, so $\mathrm{Gdim}(C)$ and $\mathrm{DSdim}(C)$ are at most $4\,\mathrm{Ndim}(C)(\lfloor \log_2 k\rfloor + 2)$ and all three dimensions are finite together. Moreover, if $\mathrm{Gdim}(C) \le d$ and $\beta$ is finite, $C$ realizes at most $\sum_{i \le d}\binom{nk}{i}$ labelings on any $n$ points. For binary labels all three coincide with the VC dimension, and every pseudo-cube on a finite coordinate set $\iota$ has at least $2^{|\iota|}$ elements.

## Proof sketch

An N-shattered set carries an embedded Boolean cube, which is a pseudo-cube; walking along coordinate neighbours of a pseudo-cube from any anchor labeling realizes every agree/disagree pattern, giving G-shattering. For the quantitative bound, a G-shattered set $W$ yields $2^{|W|}$ distinct labelings, while Natarajan's lemma bounds them by $\sum_{i \le d}\binom{|W|}{i}\binom{k}{2}^i$; comparing growth rates gives $|W| \le 4d(\lfloor\log_2 k\rfloor + 2)$.

## Depends on

- [Graph dimension of a multiclass concept class](graph-dimension.md)
- [DS dimension characterizes multiclass PAC learnability](../../ds-dimension-characterizes-multiclass-pac-learnability.md)
- [Natarajan dimension at most d](../../../../not-yet-classified/natarajan/ndim-le.md)
- [N-shattering](../../../../not-yet-classified/natarajan/nshatters.md)

## Proof depends on

- [Natarajan's lemma](natarajans-lemma.md)

## Sources

- S. Ben-David, N. Cesa-Bianchi, D. Haussler and P. M. Long, "Characterizations of Learnability for Classes of {0, ..., n}-Valued Functions", Journal of Computer and System Sciences, 1995.
- A. Daniely and S. Shalev-Shwartz, "Optimal Learners for Multiclass Problems", Proceedings of the 27th Conference on Learning Theory (COLT), 2014.
- N. Brukhim, D. Carmon, I. Dinur, S. Moran and A. Yehudayoff, "A Characterization of Multiclass Learnability", IEEE 63rd Annual Symposium on Foundations of Computer Science (FOCS), 2022.
