# The ideal UC bit-commitment functionality

The two-party ideal functionality $\mathcal{F}_{\mathrm{com}}$ waits for $(\mathrm{commit}, b)$ from the committer, stores $b$ and notifies the receiver and the adversary that a commitment was made; on $(\mathrm{open})$ from the committer it sends $b$ to the receiver. Under static corruptions: (i) *hiding*: if only the receiver is corrupted, every interaction before opening has a law that does not depend on $b$; (ii) *binding*: once in the committed state, every subsequent activation is consistent with the stored $b$; (iii) a corrupted committer must supply its bit to $\mathcal{F}_{\mathrm{com}}$ at commitment time, so any simulator for a corrupted committer must *extract* the committed bit, and any simulator for a corrupted receiver must be able to *equivocate*.

## Depends on

- [UC emulation](../uc-emulation.md)
- [Interactive machines, linking and the single-token execution model](uc-interactive-machines.md)

## Sources

- Ran Canetti and Marc Fischlin, "Universally Composable Commitments", Advances in Cryptology – CRYPTO 2001, 2001.
- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
