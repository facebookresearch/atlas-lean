# Fingerprinting security

A fingerprinting code is secure against coalitions of size at most
$c$ with completeness error $\gamma$ and soundness error $\xi$, two nonnegative real numbers, when
for every nonempty coalition $S$ with $|S| \le c$ and every pirate strategy of $S$ the tracing game
satisfies $\Pr[w \in F(C_S) \wedge a = \bot] \le \gamma$ and $\Pr[a \in [n] \setminus S] \le \xi$.

This is Definition 3.1 of Bun, Ullman and Vadhan with separate errors, as in their
Definition 3.12, for nonempty coalitions of size at most $c$, as in Tardos's Definition 1.1. Their
Definition 3.1 asks for every coalition $S \subseteq [n]$, the empty one included, with
$\gamma = \xi \in (0, 1]$; it implies this predicate for $c = n$ and $\gamma = \xi$, but not
conversely. For one user, the code that always accuses that user meets this predicate with errors
$0$, while against the empty coalition, which sees no codeword, it accuses an innocent user with
probability $1$, so it has security $\xi$ in their sense only for $\xi = 1$. Their
Definition 3.12, for general query families, asks for coalitions with $|S| \ge n - 1$.

## Sources

- M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Definitions 3.1 and 3.12.
- G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008, Definition 1.1.
