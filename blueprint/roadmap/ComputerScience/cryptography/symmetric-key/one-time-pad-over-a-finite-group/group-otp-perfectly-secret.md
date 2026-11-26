# The group one-time pad is perfectly secret

Let $G$ be a finite group. The group
one-time pad on $G$ is perfectly secret: for every probability distribution on messages in $G$
and every ciphertext $c$ that occurs with positive probability, the conditional distribution
of the message given that the ciphertext is $c$ equals the prior distribution of the message.

## Sources

- J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014, Lemma 11.15.
