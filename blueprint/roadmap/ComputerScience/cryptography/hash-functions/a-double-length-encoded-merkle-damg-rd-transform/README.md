# A double-length-encoded Merkle–Damgård transform on bit strings

## Cutting a bit string into blocks

- [Cutting at most k blocks off a bit string](blocks-fuel.md)
- [Cutting a bit string into blocks](blocks.md)
- [Unblocks](unblocks.md)
- [Cutting loses nothing](unblocks-blocks.md)
- [Number of blocks of a bit string](length-blocks-le.md)

## Padding into blocks

- [Padded blocks of a message](pad-blocks.md)
- [Padding into blocks is injective](pad-blocks-injective.md)
- [Unpadding recovers the message](unpad-unblocks-pad-blocks.md)
- [Short messages have few padded blocks](length-pad-blocks-lt.md)

## The full hash and the collision reduction

- [The double-length-encoded Merkle–Damgård hash](full-hash.md)
- [Extracting a compression collision from a full-hash collision](find-collision-full-hash.md)
- [Full Collision Game](full-collision-game.md)
- [Block Adversary](block-adversary.md)
- [Full-hash collisions are block-level collisions](full-collision-game-le-hash-collision-ga.md)
- [The full Merkle-Damgård hash preserves collision resistance](full-collision-game-le.md)

## Keyed form, in the Framework hash games

- [Msg](msg.md)
- [Keyed full Merkle-Damgård hash family](md-family.md)
- [Compression-collision reduction](md-reduction.md)
- [Collision resistance of the full Merkle-Damgård hash family](coll-advantage-md-family-le.md)
- [Collision resistance of Merkle-Damgård with n-bit length fields](coll-advantage-block-count-le.md)
