# Oracles of the chosen-ciphertext experiment

For a key $k$ and an optional challenge ciphertext $c^*$, the oracles answer an encryption query $m$
with a fresh sample of $\mathrm{Enc}_k(m)$, and a decryption query $c$ with $\mathrm{Dec}_k(c)$,
except that they answer $\bot$ when $c = c^*$.
