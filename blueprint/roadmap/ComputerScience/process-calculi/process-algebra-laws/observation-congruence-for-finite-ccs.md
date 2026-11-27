# Complete axiomatization of observation congruence for finite CCS

Let $\Lambda = \Delta \cup \bar\Delta$ consist of the names in an infinite set $\Delta$ and their conames, with $\bar{\bar\alpha} = \alpha$. Consider the finite terms built from $\mathrm{NIL}$, prefixing $\mu.p$ by $\mu \in M$, choice $p + q$, parallel composition $p \mid q$, and the postfix operators $p[S]$ for partial functions $S : M \rightharpoonup M$ with $S\tau = \tau$, which cover relabelling and restriction. Their transitions are those of prefixing and choice together with: if $p \xrightarrow{\mu} p'$ then $p \mid q \xrightarrow{\mu} p' \mid q$ and $q \mid p \xrightarrow{\mu} q \mid p'$; if $p \xrightarrow{\lambda} p'$ and $q \xrightarrow{\bar\lambda} q'$ then $p \mid q \xrightarrow{\tau} p' \mid q'$; and if $p \xrightarrow{\mu} p'$ and $S\mu$ is defined then $p[S] \xrightarrow{S\mu} p'[S]$. Let $M = \Lambda \cup \{\tau\}$, where $\tau$ is the silent action. For $\lambda \in \Lambda$ write $p \xRightarrow{\lambda} p'$ if $p \xrightarrow{\tau}{}^m \xrightarrow{\lambda} \xrightarrow{\tau}{}^n p'$ for some $m, n \ge 0$. *Weak observational equivalence* $\approx$ is the [stratified observational equivalence](../hennessy-milner-logic/observational-equivalence-by-stratification.md) for the experiment relations $\xRightarrow{\lambda}$, $\lambda \in \Lambda$, and *observational congruence* $\approx_c$ is the largest congruence contained in $\approx$: $p \approx_c q$ if $C[p] \approx C[q]$ for every context $C$.

Then $\approx_c$ on these terms is exactly the congruence induced by the axioms

- (A1)–(A4): $+$ is associative, commutative and idempotent with unit $\mathrm{NIL}$;
- (A5) $x + \tau x = \tau x$;
- (A6.1) $\mu(x + \tau y) = \mu(x + \tau y) + \mu y$ and (A6.2) $\mu \tau y = \mu y$, for every $\mu \in M$;
- (A7) the expansion law: if $u = \sum_i \mu_i x_i$ and $v = \sum_j \nu_j y_j$, then $u \mid v = \sum_i \mu_i (x_i \mid v) + \sum_j \nu_j (u \mid y_j) + \sum_{\mu_i = \bar\nu_j} \tau (x_i \mid y_j)$;
- (A8) $(\mu x)[S] = (S\mu)(x[S])$ if $S\mu$ is defined, and $\mathrm{NIL}$ otherwise; (A9) $(x + y)[S] = x[S] + y[S]$; (A10) $\mathrm{NIL}[S] = \mathrm{NIL}$.

The axiom $\mu(x + \tau y) = \mu(x + y) + \mu y$, which is complete without parallel composition, is not sound for $\approx_c$ in the presence of $\mid$. As for [the fragment without relabelling](observation-congruence-with-parallel-composition.md), the completeness proof needs a name occurring in neither of the two terms compared, so $\Delta$ is infinite.

## Depends on

- [Observational equivalence by stratification](../hennessy-milner-logic/observational-equivalence-by-stratification.md)
- [Complete axiomatization of observation congruence for finite sums](observation-congruence-for-finite-sums.md)

## Proof depends on

- [Complete axiomatization of observation congruence with parallel composition](observation-congruence-with-parallel-composition.md)

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>: Section 4.1 (the operator $\mid$ and axiom (A7)), Section 4.2 (the failure of (A6) in the presence of $\mid$, the axioms (A6.1) and (A6.2), Theorem 4.2), Section 5 (the operators $[S]$, axioms (A8)–(A10) and Theorem 5.2), Figure 1, Table I, and Appendix C3.1, which obtains Theorem 5.2 by adapting the proof of Theorem 4.2 and uses (A8)–(A10) to eliminate $[S]$.
