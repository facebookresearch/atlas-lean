# Error-robust fingerprinting security

A fingerprinting code is secure against coalitions of
size at most $c$, robustly to a $\beta$ fraction of errors, with completeness error $\gamma$ and
soundness error $\xi$, three nonnegative real numbers, when for every nonempty coalition $S$ with
$|S| \le c$ and every pirate strategy of $S$ the tracing game satisfies
$\Pr[w \in F_\beta(C_S) \wedge a = \bot] \le \gamma$ and $\Pr[a \in [n] \setminus S] \le \xi$.

This is Definition 3.3 of Bun, Ullman and Vadhan with separate errors, for nonempty coalitions of
size at most $c$. Their definition asks for every coalition $S \subseteq [n]$, the empty one
included, with $\gamma = \xi \in [0, 1]$ and $\beta \in [0, 1]$.

## Sources

- M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Definition 3.3.
