# Virtual surplus maximization is monotone

Let $X \subseteq \mathbb{R}_{\ge 0}^n$ be a feasible set of allocations and $\phi_1, \dots, \phi_n$ nondecreasing virtual value functions. Fix bidder $i$ and the other
values $v_{-i}$. If $x \in \arg\max_{x \in X} \sum_j \phi_j(v_j) x_j$ at $v = (v_i, v_{-i})$ and $x' \in \arg\max_{x \in X} \sum_j \phi_j(v'_j) x_j$ at
$v' = (v'_i, v_{-i})$ with $\phi_i(v'_i) > \phi_i(v_i)$, then $x'_i \ge x_i$. Hence the allocation to $i$ of any virtual surplus maximizer is nondecreasing in $v_i$
whenever $\phi_i$ is strictly increasing. When $\phi_i$ is only nondecreasing, as for regular distributions, the allocation to $i$ is nondecreasing in $v_i$
provided ties among maximizers are broken by a rule that depends on $v$ only through the vector $(\phi_j(v_j))_j$; with ties broken otherwise it
need not be.

## Proof

Add the two optimality inequalities $\sum_j \phi_j(v_j) x_j \ge \sum_j \phi_j(v_j) x'_j$ and $\sum_j \phi_j(v'_j) x'_j \ge \sum_j \phi_j(v'_j) x_j$; the terms for
$j \ne i$ cancel, leaving $(\phi_i(v'_i) - \phi_i(v_i))(x'_i - x_i) \ge 0$. If $\phi_i(v'_i) = \phi_i(v_i)$, the two virtual value vectors coincide and such a tie-breaking rule
selects the same allocation.

## Related topics

- [Optimal auctions for regular distributions](remaining-clauses-of-optimal-auctions-for-regular-distributi.md)

## Sources

- J. D. Hartline, *Mechanism Design and Approximation*, Chapter 3, Lemma 3.3.1 (monotone virtual values give a monotone allocation for the virtual surplus maximizer $\mathrm{OPT}(\phi(v))$, a function of the virtual value profile) and Definition 3.3.1 (regular: nondecreasing virtual value). <https://jasonhartline.com/MDnA/MDnA-ch3.pdf>
