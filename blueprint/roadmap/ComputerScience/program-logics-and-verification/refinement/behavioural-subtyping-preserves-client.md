# Behavioural subtyping preserves client correctness

A *method contract* is a pair $(\mathit{pre}, \mathit{post})$ of a predicate $\mathit{pre}$ on states and a relation $\mathit{post}$ between initial and final
states. A method implementation, given by a big-step relation $\sigma \Downarrow \sigma'$, *satisfies* the contract if every terminating execution
$\sigma \Downarrow \sigma'$ with $\mathit{pre}(\sigma)$ has $\mathit{post}(\sigma, \sigma')$.

**Theorem.** Let a type $T$ give a method the contract $(\mathit{pre}_T, \mathit{post}_T)$ and a subtype $S$ give it $(\mathit{pre}_S, \mathit{post}_S)$, with

- $\mathit{pre}_T(\sigma) \Rightarrow \mathit{pre}_S(\sigma)$ for every state $\sigma$, and
- $\mathit{pre}_T(\sigma) \wedge \mathit{post}_S(\sigma, \sigma') \Rightarrow \mathit{post}_T(\sigma, \sigma')$ for all states $\sigma, \sigma'$.

Then every implementation that satisfies the contract of $S$ also satisfies the contract of $T$. Consequently, for a client program
whose correctness proof uses only the contracts of $T$ for its method calls, through a proof rule for calls that is sound for every
implementation satisfying those contracts, the proved triples remain valid when the calls run the implementations of $S$.

The proof is one line: from $\mathit{pre}_T(\sigma)$ and $\sigma \Downarrow \sigma'$, the first condition gives $\mathit{pre}_S(\sigma)$, satisfaction gives
$\mathit{post}_S(\sigma, \sigma')$, and the second condition gives $\mathit{post}_T(\sigma, \sigma')$. Liskov and Wing's methods rule, a pre-condition rule
$\mathit{pre}_T \Rightarrow \mathit{pre}_S$ and a post-condition rule $\mathit{post}_S \Rightarrow \mathit{post}_T$ (modulo an abstraction function from subtype to
supertype values), implies both conditions.

## Expansion

Fix a client language with method calls, its semantics and the contract-based call rule, and prove that rule sound for every
implementation satisfying the contracts, so that the consequence about clients is a theorem rather than a remark.

## Sources

- B. H. Liskov and J. M. Wing, "A behavioral notion of subtyping", *ACM Transactions on Programming Languages and Systems* 16(6):1811–1841, 1994, <https://www.cs.cmu.edu/~wing/publications/LiskovWing94.pdf>: Section 5.2 (definition of the subtype relation: methods rule with pre-condition and post-condition rules, Figure 4) and Section 5.2.2 (informal justification of the subtype requirement).
