# Simulating the first round with relation input servers

Fix $k>0$ encoded relations, a reporting query $q$, its valid inputs, $R\geq1$ rounds and $0\leq\varepsilon\leq1$. Fix a nonempty public domain $\mathcal D$ of pairs $(p,\mathbf n)$ of positive worker count and relation lengths in bits. Use **the same** $\mathcal D$, input size $M=\sum_j n_j$, common seed law and tolerance function $\eta:\mathcal D\to[0,1)$ in both input conventions. The domain and tolerance do not depend on the payload, schedule or random draw.

Suppose a distributed protocol family reports $q$ throughout $\mathcal D$ with cap constant $C$. The following are additional hypotheses, not consequences of the definition of reporting:

1. For every pair in $\mathcal D$, $k$ divides $p$ and there is a fixed public balanced wiring that allocates each relation's positions to its own group of $p/k$ workers. Each group's initial shards can be read from that relation alone. The distributed protocol's guarantee includes this layout on every valid payload.
2. There are fixed relation-local encoders, local recipient decoders and a single constant $C'>0$ throughout $\mathcal D$. Each input server uses only the public parameters, the seed and its own relation to form one packet per recipient. For every valid payload and draw on which the original first barrier fits, those packets reconstruct each recipient's complete first post-barrier view, including its retained initial shard. Each recipient can decode using its packets, seed and public parameters; lengths, sender identities and other framing are accounted for. The sum of packet lengths at each recipient is at most $C'M/p^{1-\varepsilon}$.
3. The resulting success events are measurable; in particular this holds for seed-measurable encoding, decoding and local operations on these discrete transcripts with finite reports.

Then there is a separate-input protocol family reporting $q$ on $\mathcal D$ in $R$ rounds at the same $\varepsilon$ and $\eta$. In the first round each relation server simulates its group's local computations and sends the packets; afterward it is silent. Each worker decodes its simulated view and continues the original worker rounds. A cap constant of $\max(C,C')$ preserves **each successful draw** of the original protocol, so the per-input success probability cannot decrease. This gives the separate-to-distributed direction for lower bounds where the hypotheses hold; it does not establish them for a particular source theorem.

**Why the domain matters.** On the all-pairs domain, take one relation with a one-bit membership query and $\varepsilon=0$. For any proposed cap constant $C>0$, choose $p>C$. At $M=1$ the cap is then zero. A distributed worker can report its local bit without a send. In the separate convention, completed runs give every worker empty initial input and all-empty inboxes. At a fixed seed the two bit values cannot both yield a correct report (abort is failure), so the two success probabilities cannot both exceed $1/2$. This counterexample to an unrestricted exact-cap transfer does not apply to domains that exclude those pairs and is not a query-dependent asymptotic lower bound.

## Depends on

- [Query reporting with public raw-bit layouts](../parallel-query-communication/raw-position-communication.md)

## Proof depends on

- [Completed separate-input runs at zero receive cap](../parallel-query-communication/separate-zero-cap.md)

## Sources

- Paul Beame, Paraschos Koutris and Dan Suciu, *Communication Steps for Parallel Query Processing*, PODS 2013, §2.4 (grouped initial distribution). The explicit common domain, bit-packing hypotheses and zero-cap boundary concern the concrete representation. [Authors' copy](https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf).
