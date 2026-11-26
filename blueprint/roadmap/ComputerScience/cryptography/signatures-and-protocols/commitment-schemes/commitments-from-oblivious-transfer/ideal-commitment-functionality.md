# The ideal commitment-with-abort functionality

The ideal *commitment with abort* functionality between a sender and a receiver has a private state that is empty, committed to a bit $b$, opened, or aborted. The sender may *commit* (the first commitment fixes $b$), *open* (revealing $b$ to the receiver) or *abort*; the receiver may only *poll*, which returns the public status (nothing, committed, opened with value $b$, or aborted). Polling does not change the state, and before opening, every receiver-only interaction, with arbitrary adaptive programs and private randomness, has a reply law independent of the committed bit.

## Depends on

- [The binding experiment](../the-computational-binding-game-for-keyed-commitm/binding-game.md)

## Sources

- Ran Canetti and Marc Fischlin, "Universally Composable Commitments", Advances in Cryptology – CRYPTO 2001, 2001.
- Ronald Cramer, "Introduction to Secure Computation", Revised version of the 1998 Aarhus Summer School lecture, 2000.
