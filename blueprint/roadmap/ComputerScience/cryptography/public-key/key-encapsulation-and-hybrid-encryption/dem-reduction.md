# Eavesdropper against the data-encapsulation mechanism

From an eavesdropping adversary $A$ against the hybrid scheme, the eavesdropper against the
data-encapsulation mechanism runs key generation and encapsulation itself, drawing $(pk, sk)$ and an
encapsulation $e$ together with the coins of $A$. It challenges with the messages $A$ chooses on $pk$,
and on the challenge ciphertext $c$ it guesses as $A$ does on $(e, c)$.
