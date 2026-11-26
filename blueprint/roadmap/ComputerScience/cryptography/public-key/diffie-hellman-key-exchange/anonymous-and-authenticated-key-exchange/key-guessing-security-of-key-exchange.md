# Key-guessing security of anonymous key exchange

An *anonymous key exchange* protocol is a pair of interacting probabilistic algorithms producing a transcript and a shared key. It is *secure against eavesdroppers* in the key-guessing sense if every efficient adversary given the transcript of an honest execution outputs the shared key with negligible probability. This is weaker than the indistinguishability notion, in which the key must look uniform given the transcript.

## Depends on

- [Key-exchange eavesdropping experiment](../../security-of-diffie-hellman-key-exchange/ke-game.md)

## Sources

- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd ed., CRC Press, 2020, Section 11.3.
