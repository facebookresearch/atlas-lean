# The MAC forger

Katz and Lindell's adversary against the MAC (Section 4.5), with guessed index $j$, draws
$k_1 \leftarrow \mathrm{Gen}_1$, a fair challenge bit, the chosen-ciphertext adversary's coins and the
encryption randomness (two random tapes of $q$ samples and the challenge randomness), and then runs
the simulation with guessed index $j$.
