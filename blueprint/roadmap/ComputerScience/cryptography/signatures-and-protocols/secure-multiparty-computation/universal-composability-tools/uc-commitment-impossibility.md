# Canetti–Fischlin: UC commitments are impossible in the plain model

Let $\mathcal{F}_{\mathrm{com}}$ be the ideal two-party bit-commitment functionality: the committer sends $b$, the receiver learns only that a commitment was made; later the committer may open and the receiver learns $b$. $\mathcal{F}_{\mathrm{com}}$ is hiding before opening (against a corrupted receiver, every interaction before opening has a law independent of $b$) and binding (after a commitment, every activation is consistent with the committed bit). Call a protocol *bilateral* if only the committer and the receiver send messages, and a bilateral commitment protocol *terminating* if, with non-negligible probability, the honest receiver accepts a commitment of the honest committer and outputs its receipt, and, on a valid decommitment from the honest committer, outputs the opened bit. There is no bilateral, terminating protocol in the plain model (without setup) that UC-realizes $\mathcal{F}_{\mathrm{com}}$ against static corruptions, even if the simulator may depend on the environment: for a candidate protocol, let the adversary corrupt the committer and relay messages between the environment and the honest receiver, while the environment runs the honest committer's code on a random bit; since the honest receiver outputs its receipt before any opening, the simulator must extract the committed bit during the commit phase, without rewinding the environment. A corrupted receiver facing an honest committer can then run this simulator internally on the committer's messages and guess the committed bit before any opening with probability non-negligibly above $1/2$, contradicting hiding.

## Proof sketch

In the ideal world, the simulator for a corrupted committer driven by the environment must send the committed bit to $\mathcal{F}_{\mathrm{com}}$ during the commit phase, and termination makes it do so with non-negligible probability. In a second execution, an adversary corrupting the receiver feeds the honest committer's messages to a copy of that simulator, whose answers it forwards as the receiver's; the bit the simulator submits predicts the honest committer's random bit with probability non-negligibly above $1/2$, which no ideal-world adversary can do, since before opening its view is independent of the bit.

## Depends on

- [UC emulation](../uc-emulation.md)
- [The ideal UC bit-commitment functionality](uc-commitment-functionality.md)
- [The ideal commitment-with-abort functionality](../../commitment-schemes/commitments-from-oblivious-transfer/ideal-commitment-functionality.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Sources

- Ran Canetti and Marc Fischlin, "Universally Composable Commitments", Advances in Cryptology – CRYPTO 2001, 2001.
- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
