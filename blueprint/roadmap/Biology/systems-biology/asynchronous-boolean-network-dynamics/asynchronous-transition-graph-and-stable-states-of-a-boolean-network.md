# Asynchronous transition graph and stable states of a Boolean network

**Setting.** A Boolean network on $n$ variables is a map $F = (f_1, \dots, f_n) : \{0,1\}^n \to \{0,1\}^n$, where $f_i$ is the logical rule of variable $i$.

- *Synchronous dynamics:* each state $x$ has exactly one successor $F(x)$.
- *Asynchronous dynamics:* the successors of $x$ are obtained by (1) computing $F(x)$; (2) taking the indices $i$ with $x_i \ne f_i(x)$ (the variables called to change); (3) for each such $i$, the state $(x_1, \dots, x_{i-1}, f_i(x), x_{i+1}, \dots, x_n)$, i.e. $x$ with coordinate $i$ flipped. The asynchronous transition graph has an arc from each state to each of its asynchronous successors.

**Statements.**

1. The stable states (states without asynchronous successors, sinks of the asynchronous transition graph) are exactly the fixed points $F(x) = x$, which are also the stable states of the synchronous dynamics; stable states do not depend on the updating strategy.
2. Every asynchronous transition changes exactly one coordinate, so the asynchronous transition graph is a subgraph of the $n$-dimensional hypercube graph, each state has at most $n$ successors, and no assumption is made about the relative speeds of processes: every interleaving of single-variable updates is represented.
3. Every trajectory eventually enters a terminal strongly connected component (an attractor); the stable states are the singleton attractors, and if the stable states are the only attractors, every state reaches at least one of them along some path.

## Expansion

For 1: $x$ has no asynchronous successor iff no index satisfies $x_i \ne f_i(x)$, i.e. iff $F(x) = x$, which is the definition of a synchronous fixed point. For 2: by construction a successor differs from $x$ in one coordinate; a state has as many successors as variables called to change. For 3: in the finite directed graph, following arcs from any state must reach a strongly connected component with no outgoing arcs; a terminal component with one state and no arcs is a stable state. In the death-receptor cell-fate model (25 variables, $2^{25} > 3.3 \times 10^7$ states), the 27 stable states were the sole attractors under asynchronous updating and clustered into survival (NF-κB active), apoptosis (caspase activation, mitochondrial outer membrane permeabilization), non-apoptotic death (mitochondrial permeability transition) and a naïve state; synchronous updating, by contrast, imposes simultaneous updates of all variables and can produce cyclic attractors that no single-variable interleaving realizes.

## Sources

- L. Calzone, L. Tournier, S. Fourquet, D. Thieffry, B. Zhivotovsky, E. Barillot, A. Zinovyev, "Mathematical modelling of cell-fate decision in response to death receptor engagement", PLoS Computational Biology (2010), Methods ("Boolean formalism, synchronous vs. asynchronous strategy") and Results ("Identification of stable states"), <https://doi.org/10.1371/journal.pcbi.1000702> (PMC2832675).
