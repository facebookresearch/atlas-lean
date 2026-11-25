# Signature scheme

A signature scheme (Katz and Lindell, Definition 12.1) consists of a key-generation distribution
$\mathrm{Gen}$ on pairs $(pk, sk)$ of a public key and a secret key; a probabilistic signing
algorithm, giving for each secret key $sk$ and message $m$ a distribution $\mathrm{Sign}_{sk}(m)$ on
signatures; and a deterministic verification algorithm, giving for each public key $pk$, message
$m$ and signature $\sigma$ a bit $\mathrm{Vrfy}_{pk}(m, \sigma)$.
