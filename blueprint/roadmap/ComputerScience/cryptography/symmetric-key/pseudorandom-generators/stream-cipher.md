# The stream cipher

For a generator $G : S \to Y$ into an additive group $Y$ of messages (bit strings under exclusive or
are one), the stream cipher (Katz and Lindell, Construction 3.17) has a uniform seed $k \in S$ as key,
encrypts $m$ as $G(k) + m$, and decrypts $c$ as $c - G(k)$: the keystream $G(k)$ serves as a one-time
pad.
