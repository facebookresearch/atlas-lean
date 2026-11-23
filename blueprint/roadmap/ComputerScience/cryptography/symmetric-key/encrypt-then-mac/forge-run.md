# Run of the MAC forger with a guessed index

On coins $(k_1, b, r, \omega_1, x, \omega_2)$, namely a key $k_1$, a challenge bit $b$, the
adversary's coins $r$, a tape $\omega_1$ for the first stage, the challenge randomness $x$ and a tape
$\omega_2$ for the second stage, the MAC forger guessing index $j$ simulates the chosen-ciphertext
experiment with challenge bit $b$, tagging through its MAC oracle, the challenge ciphertext
included. The adversary's queries are indexed $0, 1, 2, \dots$ in order through both stages,
encryption and decryption queries alike; tagging the challenge does not count. The forger outputs
the query with index $j$ if that is a decryption query, and otherwise the challenge ciphertext,
which loses.
