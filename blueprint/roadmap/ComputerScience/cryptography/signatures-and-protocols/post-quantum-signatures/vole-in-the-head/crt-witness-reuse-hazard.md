# Witness-reuse hazard when VOLE masks double as garbling offsets

Suppose a VOLE-in-the-head prover reuses the first $\lambda$ bits of its witness as Free-XOR garbled-circuit label offsets within CRT-structured VOLE masks. Then the masks satisfy linear relations that leak parities of the witness: there is a test which a distinguisher knowing a candidate witness $r$ runs on the transcript to distinguish real masks from simulated ones with non-negligible advantage, even when $r$ is placed first in the witness order, so the proof is not witness-knowing zero knowledge. Reordering the witness so that the reused bits are independent of the masked positions, and an intermediate hop that decouples the CRT witness reuse, repair the simulation.

## Proof sketch

The reused bits appear both inside the VOLE correlation and as offsets in the garbled material; XORing the corresponding public values cancels the masks and exposes a parity of the witness.

## Depends on

- [VOLE-in-the-head](vole-in-the-head.md)
- [Free-XOR garbling](../../secure-multiparty-computation/boolean-garbling-constructions/free-xor-garbling.md)

## Sources

- Carsten Baum et al., "FAEST v3: Algorithm Specifications", FAEST Team, 2026.
