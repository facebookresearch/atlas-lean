# Non-uniform IVC with cost independent of the number of instructions

Using ProtoStar's accumulation together with a lookup-based selection of the executed instruction's constraints, there is an NIVC scheme for step functions $F_1,\dots,F_k$ in the random oracle model whose per-step prover cost is proportional to the size of the executed $F_j$ plus a lookup of size $O(1)$ per step, and whose recursion overhead (accumulation verifier circuit) is independent of $k$; in particular a single running accumulator suffices, in contrast with maintaining one running instance per instruction.

## Proof sketch

Express the branch selection as a special-sound protocol where the prover commits only to the executed branch's witness and uses a lookup into the table of branch selectors; accumulate as in the generic theorem. Prover messages for non-executed branches are zero and contribute no commitment cost.

## Depends on

- [ProtoStar: generic accumulation for special-sound protocols](protostar-accumulation.md)
- [Logarithmic-derivative lookups as a degree-two special-sound protocol](protostar-lookup-special-sound.md)
- [Non-uniform incrementally verifiable computation](../customizable-constraint-systems-and-multi-folding/non-uniform-ivc.md)

## Proof depends on

- [ProtoStar: generic accumulation for special-sound protocols](protostar-accumulation.md)

## Sources

- Benedikt Bünz, Binyi Chen, "Protostar: Generic Efficient Accumulation/Folding for Special-Sound Protocols", ASIACRYPT (2023), IACR ePrint 2023/620.
