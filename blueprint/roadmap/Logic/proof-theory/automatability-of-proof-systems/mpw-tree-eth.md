# Mertz–Pitassi–Wei: short tree-like resolution proofs are hard to find under ETH

Assume the Exponential Time Hypothesis. Let $Q$ be tree-like resolution or general resolution (the theorem also covers Nullstellensatz, polynomial calculus and polynomial calculus with resolution). For every constant $0 < \varepsilon < 1/7$ and every function $f(n) = o\big((\log \log n)^{1/7 - \varepsilon}\big)$, the system $Q$ is not $n^{f(n)}$-automatable: no algorithm, given an unsatisfiable CNF formula $\tau$, outputs a $Q$-refutation of $\tau$ within time $n^{f(n)}$, where $n$ bounds the number of variables of $\tau$, the size of $\tau$ and the size of its shortest $Q$-refutation.

## Proof sketch

The reduction starts from the gap hitting set problem $(\mathcal{S}, k, k^2)$ over $[n]$: decide whether the collection $\mathcal{S}$ of $n$ nonempty subsets of $[n]$ has a hitting set of size at most $k$ or every hitting set has size greater than $k^2$. Under ETH no algorithm solves it in time $n^{o(k)}$ for $k = O\big((\log \log n)^{1/7 - \varepsilon}\big)$ (a consequence of the Chen–Lin construction). A polynomial-time map sends $\mathcal{S}$ to an unsatisfiable CNF $\tau_{\mathcal{S}}$ whose shortest $Q$-refutation has size $n^{O(1)}$ when the minimum hitting set has size at most $k$, and size $n^{\Omega(k)}$ when it exceeds $k^2$. Running an $n^{f(n)}$-time automating algorithm on $\tau_{\mathcal{S}}$ for $n^{O(f)}$ steps and checking whether it returns a valid refutation decides the gap problem in time $n^{o(k)}$, contradicting ETH.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Sources

- I. Mertz, T. Pitassi, Y. Wei, "Short proofs are hard to find", ICALP (2019), LIPIcs 132, Art. 84, doi:10.4230/LIPIcs.ICALP.2019.84.
