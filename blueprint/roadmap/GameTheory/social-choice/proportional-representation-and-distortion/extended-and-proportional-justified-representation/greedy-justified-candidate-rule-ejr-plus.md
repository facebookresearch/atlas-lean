# The Greedy Justified Candidate Rule satisfies EJR+ in polynomial time

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. The Greedy Justified Candidate Rule starts with $W = \emptyset$ and, for $\ell = k, k - 1, \dots, 1$, repeatedly adds a candidate $c \notin W$ for which some group $N' \subseteq N_c$ of at least $\ell n/k$ voters has $\lvert A_i \cap W\rvert < \ell$ for all $i \in N'$, as long as such a candidate exists, then decreases $\ell$, and returns $W$ without filling it up. The rule runs in polynomial time, and its output $W$ has $\lvert W \rvert \le k$, possibly with fewer than $k$ members, and satisfies the EJR+ condition. Enlarging a set can only increase each $\lvert A_i \cap W \rvert$ and shrinks the set of candidates outside it, so the EJR+ condition passes to supersets; as a corollary, every completion of $W$ to a committee of size $k$, an arbitrary one included, satisfies EJR+ and hence EJR.

## Proof sketch

When the rule stops at level $\ell$, no witness for an EJR+ violation at level $\ell$ remains, and adding candidates later only increases $\lvert A_i \cap W\rvert$, so EJR+ holds at the end for all $\ell$. To bound the number of selected candidates, build a price system: give every voter a budget $k/n$ and, when a candidate is added at level $\ell$ because of a group $N'$ with $\lvert N' \rvert \ge \ell n/k$, split its price $1$ equally among $N'$. Each voter of $N'$ pays at most $k/(\ell n)$ for this candidate and has paid for fewer than $\ell$ earlier candidates, each at most as much, since earlier levels used groups at least as large; so no voter overspends. The total budget is $k$, hence at most $k$ candidates are selected. For the corollary, a witness $c \notin W'$ and $N'$ of an EJR+ violation by a superset $W' \supseteq W$ is also one for $W$.

## Depends on

- [EJR+ and PJR+ proportionality axioms](ejr-plus-and-pjr-plus.md)
- [Extended justified representation](extended-justified-representation.md)

## Proof depends on

- [EJR+ strengthens EJR, is verifiable in polynomial time, and is satisfied by PAV and equal shares](ejr-plus-verification-and-satisfaction.md)

## Sources

- M. Brill, J. Peters, "Robust and Verifiable Proportionality Axioms for Multiwinner Voting", EC 2023, arXiv:2302.01989.
