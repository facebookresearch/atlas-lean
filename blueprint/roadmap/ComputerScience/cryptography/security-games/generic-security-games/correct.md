# Correctness of a private-key encryption scheme

A private-key encryption scheme is correct when decryption recovers every message: for every key
$k$ in the support of $\mathrm{Gen}$, every message $m$ and every ciphertext $c$ in the support of
$\mathrm{Enc}_k(m)$, $\mathrm{Dec}_k(c) = m$ (Katz and Lindell, Definition 3.7).
