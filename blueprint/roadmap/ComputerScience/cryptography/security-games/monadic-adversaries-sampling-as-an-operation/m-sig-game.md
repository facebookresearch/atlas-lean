# Monadic signature forgery game

Let $\Sigma$ be a signature scheme with key-pair distribution $\mathrm{Gen}$, randomized signing $\mathrm{Sign}_{sk}$ and deterministic verification $\mathrm{Vrfy}_{pk}$, and let messages have decidable equality. For a [monadic signature forger](msig-forger.md) $A$, the game

1. samples a key pair $(pk, sk) \leftarrow \mathrm{Gen}$;
2. runs $A$ on $pk$, answering sampling operations by the sampling family and each signing query $m$ by a fresh sample of $\mathrm{Sign}_{sk}(m)$, and records the ordered list of query and answer pairs ([logged run](m-eval-log.md));
3. from the output $(m, \sigma)$ and that log, returns true if and only if $\mathrm{Vrfy}_{pk}(m, \sigma)$ holds **and** the message $m$ was never a signing query.

It is a distribution on Booleans. Freshness concerns the message only: a new signature on a queried message does not win. This is $\mathrm{Sig\text{-}forge}$ of Katz and Lindell, Definition 12.2, for forgers that sample on demand.
