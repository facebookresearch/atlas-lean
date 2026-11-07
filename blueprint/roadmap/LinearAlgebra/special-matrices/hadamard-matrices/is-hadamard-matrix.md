# Hadamard matrix

For a natural number $m$, an $m \times m$ matrix $H$ with integer
entries is a Hadamard matrix when every entry of $H$ is $1$ or $-1$ and
$H^{\mathsf T} H = m I$, where $I$ is the $m \times m$ identity matrix.

This predicate is used for Hadamard matrices of order $n + 1$ with circulant core, which exist
when $n$ is a prime congruent to $3$ mod $4$ (Paley) or $n = p(p + 2)$ with $p$ and $p + 2$
both prime (Stanton–Sprott/Whiteman).

## Sources

- Richard P. Brent and Adam B. Yedidia, "Computation of Maximal Determinants of Binary Circulant Matrices," Journal of Integer Sequences 21 (2018), Article 18.5.6, Theorem (label thm:circulant_core), lines 684–695, https://cs.uwaterloo.ca/journals/JIS/VOL21/Brent/brent11.tex quoting Kotsireas et al.; attributions at lines 698–704. The prime-power versions of cases (1)–(2), if the source allows them, and cases (3)–(4) of the source theorem (Singer, Hall) are not formalized here.
