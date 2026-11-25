# Hybrid encryption

Given a key-encapsulation mechanism and a private-key encryption scheme with the same keys, the
data-encapsulation mechanism, the hybrid public-key scheme (Katz and Lindell, Section 11.3) uses the
key generation of the key-encapsulation mechanism. It encrypts $m$ under $pk$ as $(e, c)$, where
$(k, e)$ is an encapsulation under $pk$ and $c \leftarrow \mathrm{Enc}_k(m)$, and it decrypts
$(e, c)$ with $sk$ by decapsulating $e$ to a key $k$ and returning $\mathrm{Dec}_k(c)$, or $\bot$ if
decapsulation fails.
