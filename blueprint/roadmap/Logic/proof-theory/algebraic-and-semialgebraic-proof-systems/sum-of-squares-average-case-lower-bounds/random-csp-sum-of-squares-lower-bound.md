# Sum-of-Squares lower bounds for refuting random CSPs

If a $k$-ary predicate $P$ supports a $t$-wise uniform distribution on its satisfying assignments, $2 \le t < k$, then Sum-of-Squares of degree about $n/(\Delta^{2/(t-1)} \log \Delta)$ fails to refute a random instance of $\mathrm{CSP}(P^{\pm})$ with $\Delta n$ constraints; more generally SoS cannot $(\delta_P(t)+o(1))$-refute it.

For a predicate $P : \{0,1\}^k \to \{0,1\}$ let $P^{\pm}$ be the $2^k$ predicates obtained by negating inputs. A random instance of $\mathrm{CSP}(P^{\pm})$ with density $\Delta$ has $n$ variables and $m = \Delta n$ constraints, each a uniformly random member of $P^{\pm}$ on a uniformly random scope of $k$ distinct variables. A distribution on $\{0,1\}^k$ is **$t$-wise uniform** if its marginal on every $t$ coordinates is uniform. For $1 < t \le k$,

$$
\delta_P(t) = \min \, d_{\mathrm{TV}}(\mu, \sigma)
$$

over $t$-wise uniform $\mu$ and distributions $\sigma$ supported on satisfying assignments of $P$. A $\delta$-refutation certifies that at most a $(1 - \delta)$ fraction of the constraints is simultaneously satisfiable; weak refutation certifies unsatisfiability.

**Theorem (weak refutation).** Let $3 \le \tau \le k$ be such that $P$ supports a $(\tau - 1)$-wise uniform distribution on $\{0,1\}^k$ supported on $P^{-1}(1)$ but supports no $\tau$-wise uniform distribution on $P^{-1}(1)$; equivalently, $P$ supports a pairwise uniform distribution on its satisfying assignments and $\tau = \tau(P)$ is the least integer $3 \le \tau \le k$ for which it supports no $\tau$-wise uniform one. Let $0 < \beta < 1/2$. If $\mathcal{I}$ is a random instance of $\mathrm{CSP}(P^{\pm})$ with $m = \Delta n$ constraints and $\Delta \ge 10$, then, except with probability at most $\beta$, degree-$D$ SoS fails to refute $\mathcal{I}$, where

$$
D = \frac{\beta^{O(1/\tau)}}{k \cdot 2^{O(k/\tau)}} \cdot \frac{n}{\Delta^{2/(\tau - 2)} \log \Delta} .
$$

The $(\tau - 1)$-wise uniformity hypothesis cannot be dropped: the 3-AND predicate has a single satisfying assignment, so it supports no pairwise uniform distribution, and at constant density two of its constraints conflict on a shared variable with high probability, giving a constant-degree refutation.

**Theorem ($\delta$-refutation).** Let $1 < t \le k$, let $0 < \beta < 1/2$ and let $\mathcal{I}$ be as above. Except with probability at most $\beta$, degree-$D$ SoS fails to $(\delta_P(t) + \epsilon)$-refute $\mathcal{I}$, where

$$
\epsilon = 2^{\frac{\log n}{2 \log \Delta}} \cdot \frac{1}{\sqrt{n}}, \qquad D = \frac{\beta^{O(1/t)}}{k \cdot 2^{O(k/t)}} \cdot \frac{n}{\Delta^{2/(t-1)} \log \Delta} .
$$

Here $\epsilon = o(1)$ always and $\epsilon = O(1/\sqrt{n})$ when $\Delta = n^{\Omega(1)}$. Both theorems hold for predicates over alphabets of size $q > 2$ with no change in parameters.

## Proof sketch

In particular constant-degree, hence polynomial-time, SoS needs $\tilde{\Omega}(n^{(t+1)/2})$ constraints to $(\delta_P(t) + o(1))$-refute, and with Lee-Raghavendra-Steurer the same holds for every polynomial-size SDP relaxation. Algorithms of Allen-O'Donnell-Witmer and Raghavendra-Rao-Schramm show the three-way trade-off among density, degree and refutation strength is tight up to lower-order factors. The pseudo-expectation is defined from planted distributions on closures of small subgraphs of the factor graph, using that a random factor graph satisfies a plausibility assumption about its small subgraphs (proved by expansion), and positive semidefiniteness is shown separately. The result subsumes all previously known lower bounds for semialgebraic refutation of random CSPs, including those for $k$-XOR and $k$-SAT.

## Depends on

- [Sums-of-Squares proof system](../sums-of-squares-proof-system.md)
- [Finite relational templates and the homomorphism problem CSP(A)](../../../../TheoryOfComputation/np-completeness/satisfiability/finite-domain-csp-dichotomy/finite-templates-and-csp-of-a.md)

## Proof depends on

None.

## Sources

- Pravesh K. Kothari, Ryuhei Mori, Ryan O'Donnell, David Witmer, "Sum of squares lower bounds for refuting any CSP", *49th ACM Symposium on Theory of Computing (STOC 2017)*, 2017, https://doi.org/10.1145/3055399.3055485; numbering of arXiv:1701.04521v1 (Theorems 1.1, 1.2 and 1.4, Corollary 1.5, Definition 2.2, Section 2.1 after Notation 2.4 for the $(\tau-1)$-wise uniformity hypothesis, Theorem 4.12 for $0 < \beta < 1/2$, Theorem 6.1, Theorems 7.1 and 7.2).
