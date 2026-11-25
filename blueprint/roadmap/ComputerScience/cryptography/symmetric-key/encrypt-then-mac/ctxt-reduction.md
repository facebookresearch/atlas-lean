# MAC forger from a ciphertext forger

From a ciphertext forger against encrypt-then-MAC and a number $q$, the MAC forger draws
$k_1 \leftarrow \mathrm{Gen}_1$, the ciphertext forger's coins and a random tape of $q$ samples of
the encryption randomness. It runs the simulation of the ciphertext forger with its MAC oracle and
outputs the forged ciphertext $(c, t)$ as a forgery of the tag $t$ on $c$.
