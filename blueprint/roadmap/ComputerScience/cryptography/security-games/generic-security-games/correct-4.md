# Correctness of a signature scheme

A signature scheme is correct when honest signatures verify: for every key pair $(pk, sk)$ in the
support of $\mathrm{Gen}$, every message $m$ and every signature $\sigma$ in the support of
$\mathrm{Sign}_{sk}(m)$, $\mathrm{Vrfy}_{pk}(m, \sigma) = 1$ (Katz and Lindell, Definition 12.1).
