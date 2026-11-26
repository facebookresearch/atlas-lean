# Canetti–Fischlin: UC commitments are impossible in the plain model

Let $\mathcal{F}_{\mathrm{com}}$ be the ideal two-party bit-commitment functionality: the committer sends $b$, the receiver learns only that a commitment was made; later the committer may open and the receiver learns $b$. $\mathcal{F}_{\mathrm{com}}$ is hiding before opening (against a corrupted receiver, every interaction before opening has a law independent of $b$) and binding (after a commitment, every activation is consistent with the committed bit). There is no two-party protocol in the plain model (without setup) that UC-realizes $\mathcal{F}_{\mathrm{com}}$ against static corruptions: for a candidate protocol, the environment can run the honest committer's code with a corrupted receiver relayed to an external honest receiver, so the simulator, which must extract the committed bit without rewinding, would also extract from the honest committer, contradicting hiding.

## Proof sketch

In the ideal world, the simulator for a corrupted committer must output the committed bit to $\mathcal{F}_{\mathrm{com}}$ during the commit phase. An environment that internally plays an honest committer against the real receiver forces the same simulator to extract a uniformly random bit from a protocol execution that, by hiding, carries no information about it.

## Depends on

- [UC emulation](../uc-emulation.md)
- [The ideal UC bit-commitment functionality](uc-commitment-functionality.md)
- [The ideal commitment-with-abort functionality](../../commitment-schemes/commitments-from-oblivious-transfer/ideal-commitment-functionality.md)

## Sources

- Ran Canetti and Marc Fischlin, "Universally Composable Commitments", Advances in Cryptology – CRYPTO 2001, 2001.
- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
