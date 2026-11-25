# Message authentication code

A message authentication code (Katz and Lindell, Definition 4.1) consists of a key-generation
distribution $\mathrm{Gen}$ on keys; a probabilistic tagging algorithm, giving for each key $k$ and
message $m$ a distribution $\mathrm{Mac}_k(m)$ on tags; and a deterministic verification algorithm,
giving for each key $k$, message $m$ and tag $t$ a bit $\mathrm{Vrfy}_k(m, t)$.
