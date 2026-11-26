# Query reporting with public raw-bit layouts

Fix a query on encoded relations and its valid inputs. Specify a domain $\mathcal D$ of public pairs $(p,\mathbf n)$, where $p>0$ is the worker count and $\mathbf n$ lists the relation lengths **in bits**. Specify a failure tolerance $\eta(p,\mathbf n)$ on this domain. Neither specification receives the payload, layout, random seed or protocol as an argument. A single number $\eta_0$ means the constant tolerance function. An empty domain tests no inputs.

In the distributed convention a schedule is a bijection from worker slots to relation/offset pairs, with slot counts differing by at most one. Each worker reads the actual bits at its positions. In the separate convention the workers start empty, and each input server holds its own relation word. Each worker computes from its initial word, the common input-independent seed, and its private history of sender-indexed deliveries. Sends use the old views; new messages are available at the next local computation. Input servers send only in the first round. Local data are retained without sending a message to oneself.

A protocol family reports the query in $R$ rounds at exponent $0\leq\varepsilon\leq1$ if there is **one** constant $C>0$ such that for every $(p,\mathbf n)\in\mathcal D$, the tolerance is in $[0,1)$ and the following holds for every schedule and every valid payload of that shape. The receive cap is the natural-number floor of $CM/p^{1-\varepsilon}$, where $M=\sum_j n_j$. The load is the maximum over recipients of the sum of all incoming message lengths. An over-cap proposal aborts before delivery; delivered traffic respects the cap even on aborted draws. Under one common probability law, the event of completion with the union of the workers' finite reports exactly equal to the answer is measurable and has probability at least $1-\eta(p,\mathbf n)$.

Choosing all pairs is stronger than choosing a large-input regime: at fixed $M$ and $\varepsilon<1$, the exact cap eventually vanishes as $p$ grows. Conversely, $p\leq M$ is one possible domain, not a premise attributed to the source. Which pairs and probabilities a theorem covers are part of that theorem's statement.

## Sources

- Paul Beame, Paraschos Koutris and Dan Suciu, *Communication Steps for Parallel Query Processing*, PODS 2013, §§2.1–2.4. Public position layouts, integer balance, exact caps, abort-before-delivery and the explicit parameter domain are conventions of this interface. [Authors' copy](https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf).
