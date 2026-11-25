# CPA adversary

A CPA adversary with coins in $R$, against an encryption oracle that takes
messages in $Y$ and returns ciphertexts in $X \times Y$, assigns to each $r \in R$ an adaptive
oracle algorithm with access to the encryption oracle that outputs two challenge messages
$(m_0, m_1) \in Y \times Y$ together with a second adaptive oracle algorithm, again with access to
the encryption oracle, which takes the challenge ciphertext in $X \times Y$ and outputs a guess
for the challenge bit.
