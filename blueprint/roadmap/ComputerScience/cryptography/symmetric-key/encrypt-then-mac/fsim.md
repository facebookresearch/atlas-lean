# The MAC forger's simulation of the chosen-ciphertext game

For a guessed index $j$, a key $k_1$, an optional challenge and a tape, the forger runs a
chosen-ciphertext adversary, starting from a given table and a given value of its query counter.
Every query, encryption or decryption, advances the counter by one and uses up one tape entry; once
the tape is used up, a fixed default entry takes the place of the next one. An encryption query $m$
with tape entry $r$ is answered by $(c, t)$, where $c = E(k_1, m, r)$ and $t$ is the MAC oracle's tag
on $c$, and the answer is recorded in the table with $m$. A decryption query is answered by the
simulated decryption oracle for the challenge and the current table, except that if the counter
equals $j$ when it is asked, the forger stops and outputs that ciphertext as its forgery. If the
adversary stops first, a given final stage takes over, from the adversary's output and the current
table and counter.
