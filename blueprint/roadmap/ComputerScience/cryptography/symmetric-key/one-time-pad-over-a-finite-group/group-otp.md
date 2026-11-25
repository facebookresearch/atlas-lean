# The group one-time pad

Let $G$ be a finite group. The group one-time pad on $G$ is the
private-key encryption scheme with messages, keys and ciphertexts in $G$ whose key $k$ is drawn
uniformly from $G$, which encrypts a message $m$ as $k m$, and which decrypts a ciphertext $c$
as $k^{-1} c$.
