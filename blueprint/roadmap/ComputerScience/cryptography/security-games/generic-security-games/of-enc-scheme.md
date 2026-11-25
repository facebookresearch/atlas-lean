# Encryption schemes with total decryption as private-key schemes

An encryption scheme in the sense of Katz and Lindell, Definition 2.1, has key generation,
encryption and a decryption that always returns a message, and is correct by definition; it need not
be perfectly secret. Every such scheme is a private-key encryption scheme with the same key
generation, encryption and decryption; in particular its decryption never outputs $\bot$.
