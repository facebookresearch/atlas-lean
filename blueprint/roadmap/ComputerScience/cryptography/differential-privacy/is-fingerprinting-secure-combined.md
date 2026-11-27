# Combined fingerprinting security

A fingerprinting code is secure against coalitions of
size at most $c$ with combined error $\varepsilon$, a nonnegative real number, when for every
nonempty coalition $S$ with $|S| \le c$ and every pirate strategy of $S$ the tracing game satisfies
$\Pr[w \in F(C_S) \wedge a \notin S] \le \varepsilon$, where $a \notin S$ means that $a$ is $\bot$
or an innocent user.

Vadhan's Definition 5.17 bounds the same event for every coalition by a negligible function of
$n$; here the bound is a fixed $\varepsilon$ and coalitions are nonempty of size at most $c$.
Tardos's Definition 1.1 bounds the probability that tracing accuses nobody or an innocent user,
for pirate strategies whose words satisfy the marking condition.

## Sources

- S. Vadhan, *The complexity of differential privacy*, in *Tutorials on the Foundations of Cryptography*, Springer, 2017, Definition 5.17 in the author's version of 9 August 2016.
- G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008, Definition 1.1.
