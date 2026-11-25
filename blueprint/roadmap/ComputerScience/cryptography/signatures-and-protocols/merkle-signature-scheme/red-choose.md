# The reduction's Lamport signing query

The reduction asks its single Lamport signing query on the forger's $j$-th signing query, found by
running the forger against its own signer, since the simulation up to that query needs no signature
under the challenge key. If the forger asks fewer queries, the reduction asks on the bitwise
complement of the forger's output message.
