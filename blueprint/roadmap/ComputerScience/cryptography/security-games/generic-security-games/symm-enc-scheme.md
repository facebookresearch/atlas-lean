# Private-key encryption scheme

A private-key encryption scheme consists of a key-generation distribution $\mathrm{Gen}$ on keys; a
probabilistic encryption algorithm, giving for each key $k$ and message $m$ a distribution
$\mathrm{Enc}_k(m)$ on ciphertexts; and a deterministic decryption algorithm, giving for each key
$k$ and ciphertext $c$ either a message $\mathrm{Dec}_k(c)$ or the error symbol $\bot$ (Katz and
Lindell, Definition 3.7). Correctness is a separate condition, so insecure and toy schemes, and
schemes that are correct only with overwhelming probability, are schemes too.
