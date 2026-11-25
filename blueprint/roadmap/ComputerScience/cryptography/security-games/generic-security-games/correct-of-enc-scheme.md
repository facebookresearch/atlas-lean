# Encryption schemes with total decryption give correct private-key schemes

Let an encryption scheme in the sense of Katz and Lindell, Definition 2.1, be given; its decryption
always returns a message, and it need not be perfectly secret. The private-key encryption scheme
with the same key generation, encryption and decryption is correct: for every key $k$ in the support
of $\mathrm{Gen}$, every message $m$ and every ciphertext $c$ in the support of $\mathrm{Enc}_k(m)$,
$\mathrm{Dec}_k(c) = m$. This holds because the original scheme is correct by definition.
