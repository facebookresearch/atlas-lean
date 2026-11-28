# Natarajan, DS and graph dimensions compared

For every class $C$ of functions $X \to \beta$,

$$
\mathrm{Ndim}(C) \le \mathrm{DSdim}(C) \le \mathrm{Gdim}(C),
$$

where $\mathrm{Ndim}$ is the Natarajan dimension and $\mathrm{DSdim}$ the Daniely-Shalev-Shwartz dimension (largest set on which the restriction of $C$ contains a pseudo-cube) (Daniely and Shalev-Shwartz, Section 5: "the new dimension is bounded between the Natarajan and Graph dimensions"; Brukhim, Carmon, Dinur, Moran and Yehudayoff, Definition 6, for the pseudo-cube form of their dimension). If $\beta$ is finite with $k = n + 1 \ge 2$ labels (identified with $\{0, \dots, n\}$), then in the $\Psi$-dimension family of Ben-David, Cesa-Bianchi, Haussler and Long (with graph dimension equal to the $\Psi_G$-dimension and $\Psi_B$ the full binary family):

1. $\Psi_G$ is a distinguisher, so for every distinguisher $\Psi$ (in particular $\Psi = \Psi_G$) the $\Psi$-dimension is bounded between the Natarajan dimension and the $\Psi_B$-dimension: $\mathrm{Ndim}(C) \le d_{\Psi}(C) \le d_{\Psi_B}(C)$ (Ben-David, Cesa-Bianchi, Haussler and Long, Corollary 6);
2. the $\Psi_B$-dimension satisfies

$$
d_{\Psi_B}(C) \le 4.67\, \mathrm{Ndim}(C) \log_2 k
$$

(Ben-David, Cesa-Bianchi, Haussler and Long, Theorem 10, applied to finite restrictions of $C$). For binary labels the Natarajan and graph dimensions coincide with the VC dimension (Ben-David, Cesa-Bianchi, Haussler and Long, Section 2.3), and so does the DS dimension, since every pseudo-cube contained in $\{0,1\}^d$ is the whole Boolean cube (Brukhim, Carmon, Dinur, Moran and Yehudayoff, remark after Definition 5).

## Proof sketch

An N-shattered set carries an embedded Boolean cube, which is a pseudo-cube; walking along coordinate neighbours of a pseudo-cube from any anchor labeling realizes every agree/disagree pattern, giving G-shattering. For the quantitative bound, a $\Psi_B$-shattered set of $d_B$ indices carries at least $2^{d_B}$ restrictions, while the Natarajan-dimension bound (Theorem 9 of Ben-David, Cesa-Bianchi, Haussler and Long) bounds them by $(d_B e (n+1)^2/(2 d_N))^{d_N}$; comparing the two gives Theorem 10.

Derived (not stated in the cited sources): combining Corollary 6 and Theorem 10 gives $\mathrm{Gdim}(C) \le 4.67\,\mathrm{Ndim}(C)\log_2 k$, so all three dimensions are finite together for finite $\beta$. Also, every finite G-shattered set has at most $4\,\mathrm{Ndim}(C)(\lfloor \log_2 k\rfloor + 2)$ points, since a G-shattered set $W$ yields $2^{|W|}$ distinct labelings while Natarajan's lemma bounds them by $\sum_{i \le d}\binom{|W|}{i}\binom{k}{2}^i$. If $\mathrm{Gdim}(C) \le d$ and $\beta$ is finite, $C$ realizes at most $\sum_{i \le d}\binom{nk}{i}$ labelings on any $n$ points. Every pseudo-cube on a finite coordinate set $\iota$ has at least $2^{|\iota|}$ elements.

## Depends on

- [Graph dimension of a multiclass concept class](graph-dimension.md)
- [DS dimension characterizes multiclass PAC learnability](../../ds-dimension-characterizes-multiclass-pac-learnability.md)
- [Natarajan dimension at most d](../natarajan-dimension-and-the-natarajan-lemma/ndim-le.md)
- [N-shattering](../natarajan-dimension-and-the-natarajan-lemma/nshatters.md)

## Proof depends on

- [Natarajan's lemma](natarajans-lemma.md)

## Sources

- S. Ben-David, N. Cesa-Bianchi, D. Haussler and P. M. Long, "Characterizations of Learnability for Classes of {0, ..., n}-Valued Functions", Journal of Computer and System Sciences, 1995; technical report version UCSC-CRL-93-31, University of California, Santa Cruz, 1993, Section 2.3, Corollary 6, Theorem 9 and Theorem 10: <https://tr.soe.ucsc.edu/sites/default/files/technical-reports/UCSC-CRL-93-31.pdf>.
- A. Daniely and S. Shalev-Shwartz, "Optimal Learners for Multiclass Problems", Proceedings of the 27th Conference on Learning Theory (COLT), 2014, Section 5; open copy: <https://arxiv.org/abs/1405.2420>.
- N. Brukhim, D. Carmon, I. Dinur, S. Moran and A. Yehudayoff, "A Characterization of Multiclass Learnability", IEEE 63rd Annual Symposium on Foundations of Computer Science (FOCS), 2022, Definitions 5 and 6; open copy: <https://arxiv.org/abs/2203.01550>.
