# Increasing lucky-car counts (Lemma 18)

Number the cars and spots $0, \dots, n-1$, let
$q^{\mathrm{inc}}_n(i, j)$ be the number of weakly increasing parking functions of length $n$ in
which car $i$ prefers spot $j$ and is lucky, and let $C_m$ be the $m$-th Catalan number. For all
$i, j \in \{0, \dots, n-1\}$, $q^{\mathrm{inc}}_n(i, j) = C_i \, C_{n-i}$ if $i = j$, and
$q^{\mathrm{inc}}_n(i, j) = 0$ otherwise.

In the one-based indexing of the source the diagonal value reads $C_{i-1} C_{n-i+1}$.

## Sources

- Steve Butler et al., "Lucky Cars and Lucky Spots in Parking Functions", Lemma 18.
