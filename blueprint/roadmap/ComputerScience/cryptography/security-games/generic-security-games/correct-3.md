# Correctness of a message authentication code

A message authentication code is correct when honest tags verify: for every key $k$ in the support
of $\mathrm{Gen}$, every message $m$ and every tag $t$ in the support of $\mathrm{Mac}_k(m)$,
$\mathrm{Vrfy}_k(m, t) = 1$ (Katz and Lindell, Definition 4.1).
