# The ioco conformance relation

Let $s$ be a labelled transition system with inputs $L_I$ and outputs $L_U$ and an action $\delta$ for quiescence (a state is quiescent if it enables no output and no internal action). The suspension system of $s$ adds a $\delta$-labelled self-loop at exactly the quiescent states. For a trace $\sigma$ over $L_I \cup L_U \cup \{\delta\}$, with transitions taken in the suspension system and internal $\tau$ steps skipped (weak transitions), $s \mathbin{\mathrm{after}} \sigma$ is the set of states reachable by $\sigma$, the suspension traces $\mathrm{Straces}(s)$ are the traces with $s \mathbin{\mathrm{after}} \sigma \ne \emptyset$, and $\mathrm{out}(Q)$ is the set of outputs and $\delta$ enabled in states of $Q$. For an input-enabled implementation $i$ and a specification $s$ that need not be input-enabled, $i \mathrel{\mathbf{ioco}} s$ holds if and only if $\mathrm{out}(i \mathbin{\mathrm{after}} \sigma) \subseteq \mathrm{out}(s \mathbin{\mathrm{after}} \sigma)$ for every $\sigma \in \mathrm{Straces}(s)$.

## Depends on

- [Reachability in a labelled transition system is transitive](../../process-calculi/labelled-transition-systems/trans.md)

## Sources

- J. Tretmans, "Model based testing with labelled transition systems", in *Formal Methods and Testing*, LNCS 4949, Springer, 2008, Section 3.4, Definitions 8 and 9, and Section 4.1, Definitions 11 and 12
