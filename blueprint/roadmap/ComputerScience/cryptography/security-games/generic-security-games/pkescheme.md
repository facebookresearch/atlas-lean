# Public-key encryption scheme

A public-key encryption scheme (Katz and Lindell, Definition 11.1) consists of a key-generation
distribution $\mathrm{Gen}$ on pairs $(pk, sk)$ of a public key and a secret key; a probabilistic
encryption algorithm, giving for each public key $pk$ and message $m$ a distribution
$\mathrm{Enc}_{pk}(m)$ on ciphertexts; and a deterministic decryption algorithm, giving for each
secret key $sk$ and ciphertext $c$ either a message $\mathrm{Dec}_{sk}(c)$ or $\bot$.
