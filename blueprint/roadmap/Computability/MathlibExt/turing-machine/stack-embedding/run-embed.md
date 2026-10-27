---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Embedding.run_embed
---

# Run embedding

**Run embedding.** A run of the sub-machine ending at a live label is a run of the host of the
same length, from any host stacks agreeing with the sub-machine's; at the end the host agrees with
the sub-machine on the image of `e` and is unchanged outside it.

## Depends on

- [Agree](agree.md)
- [Embeds](embeds.md)
- [Frame](frame.md)
- [SEmb](semb.md)
- [Run](../program/part-01/run.md)

## Proof depends on

- [Map S](map-s.md)
- [Step Aux map S](step-aux-map-s.md)
- [Iter none](../program/part-01/iter-none.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.StackEmbedding](../../../../../sources/v2/MathlibExt.md)
