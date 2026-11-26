# The Method of Equal Shares satisfies extended justified representation and priceability

An approval election consists of a finite set $N$ of $n$ voters, a finite set $C$ of candidates, approval ballots $A_i \subseteq C$ for $i \in N$, and a committee size $k$ with $1 \le k \le \lvert C \rvert$; a committee is a set $W \subseteq C$ with $\lvert W \rvert = k$. The committee chosen by the Method of Equal Shares before completion is priceable, and every committee containing it (in particular every completion) provides EJR. The method runs in polynomial time.

## Proof sketch

Priceability: the payments made in each step define $\pi_i$, all equal to $p = 1$ per elected candidate, and the stopping rule says that no unelected candidate's supporters have $1$ left. For EJR, suppose an $\ell$-cohesive group $N'$ has all members with fewer than $\ell$ representatives. Each member paid at most $\rho \le k/(\ell n)$ per candidate in every step (otherwise the common candidates of $N'$ would have been cheaper), hence each retains at least $k/n - (\ell - 1) k /(\ell n) = k/(\ell n)$, and the group can afford a common candidate, contradicting termination.

## Depends on

- [Method of Equal Shares for approval committees](method-of-equal-shares-approval.md)
- [Priceable committee in an approval election](priceable-committee.md)
- [Extended justified representation](../extended-and-proportional-justified-representation/extended-justified-representation.md)

## Sources

- D. Peters, P. Skowron, "Proportionality and the Limits of Welfarism", EC 2020, arXiv:1911.11747.
