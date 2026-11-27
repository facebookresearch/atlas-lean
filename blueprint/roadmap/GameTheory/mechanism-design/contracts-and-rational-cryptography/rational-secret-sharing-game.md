# Rational secret sharing game

In *rational secret sharing*, $n$ parties hold shares of a secret under a $(t, n)$ threshold scheme and interact to reconstruct it, each preferring outcomes in the strict order: learning the secret while some other party does not ($U^+$), all parties learning it ($U$), and not learning it ($U^-$), with $U^+ > U > U^-$. In each round parties simultaneously decide whether to broadcast their shares; a party learns the secret once it holds at least $t$ shares.

## Depends on

- [Verifiable secret sharing](../../../ComputerScience/cryptography/signatures-and-protocols/secure-multiparty-computation/verifiable-secret-sharing.md)
- [Strategic Game](../../not-yet-classified/part-02/strategic-game/strategic-game.md)

## Sources

- Joseph Y. Halpern and Vanessa Teague, "Rational Secret Sharing and Multiparty Computation: Extended Abstract", Proceedings of the Thirty-Sixth Annual ACM Symposium on Theory of Computing (STOC 2004), 2004.
- Yevgeniy Dodis and Tal Rabin, "Cryptography and Game Theory", Algorithmic Game Theory, Cambridge University Press, 2007.
