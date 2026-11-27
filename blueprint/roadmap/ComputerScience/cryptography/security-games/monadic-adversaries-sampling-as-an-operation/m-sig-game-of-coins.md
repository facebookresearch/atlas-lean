# Embedding a signature forger with explicit coins

Let messages have decidable equality. For every signature scheme and every coin signature forger $A$, the [monadic forgery game](m-sig-game.md) of its [monadic form](of-coins-5.md), which draws its coins by one sampling operation after receiving the public key, equals the coin signature forgery game of $A$ as a distribution on Booleans. Both accept if and only if the output verifies and its message was never a signing query.
