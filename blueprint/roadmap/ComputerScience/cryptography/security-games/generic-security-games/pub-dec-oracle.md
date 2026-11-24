# Decryption oracle of the public-key chosen-ciphertext experiment

For a secret key $sk$ and an optional challenge ciphertext $c^*$, the decryption oracle answers a
query $c$ with $\mathrm{Dec}_{sk}(c)$, except that it answers $\bot$ when $c = c^*$.
