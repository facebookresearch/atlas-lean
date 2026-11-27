# Correctness of a public-key encryption scheme

A public-key encryption scheme is correct when for every key pair $(pk, sk)$ in the support of
$\mathrm{Gen}$, every message $m$ and every ciphertext $c$ in the support of $\mathrm{Enc}_{pk}(m)$,
$\mathrm{Dec}_{sk}(c) = m$: the perfect correctness of Katz and Lindell, Definition 11.1.
