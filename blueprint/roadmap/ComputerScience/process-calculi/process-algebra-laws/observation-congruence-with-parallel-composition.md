# Complete axiomatization of observation congruence with parallel composition

Let $\Lambda = \Delta \cup \bar\Delta$ consist of the names in an infinite set $\Delta$ and their conames, with $\bar{\bar\alpha} = \alpha$, and let $M = \Lambda \cup \{\tau\}$, where $\tau$ is the silent action. Consider the finite terms built from $\mathrm{NIL}$, prefixing $\mu.p$ by $\mu \in M$, choice $p + q$ and parallel composition $p \mid q$, with the transitions $\mu.p \xrightarrow{\mu} p$; $p + q \xrightarrow{\mu} r$ whenever $p \xrightarrow{\mu} r$ or $q \xrightarrow{\mu} r$; $p \mid q \xrightarrow{\mu} p' \mid q$ and $q \mid p \xrightarrow{\mu} q \mid p'$ whenever $p \xrightarrow{\mu} p'$; and $p \mid q \xrightarrow{\tau} p' \mid q'$ whenever $p \xrightarrow{\lambda} p'$ and $q \xrightarrow{\bar\lambda} q'$. For $\lambda \in \Lambda$ write $p \xRightarrow{\lambda} p'$ if $p \xrightarrow{\tau}{}^m \xrightarrow{\lambda} \xrightarrow{\tau}{}^n p'$ for some $m, n \ge 0$. *Weak observational equivalence* $\approx$ is the [stratified observational equivalence](../hennessy-milner-logic/observational-equivalence-by-stratification.md) for the experiment relations $\xRightarrow{\lambda}$, $\lambda \in \Lambda$, and *observational congruence* $\approx_c$ is the largest congruence contained in $\approx$.

Then $\approx_c$ on these terms is exactly the congruence induced by the axioms

- (A1)–(A4): $+$ is associative, commutative and idempotent with unit $\mathrm{NIL}$;
- (A5) $x + \tau x = \tau x$;
- (A6.1) $\mu(x + \tau y) = \mu(x + \tau y) + \mu y$ and (A6.2) $\mu \tau y = \mu y$, for every $\mu \in M$;
- (A7) the expansion law: if $u = \sum_i \mu_i x_i$ and $v = \sum_j \nu_j y_j$, then $u \mid v = \sum_i \mu_i (x_i \mid v) + \sum_j \nu_j (u \mid y_j) + \sum_{\mu_i = \bar\nu_j} \tau (x_i \mid y_j)$.

The completeness proof uses (A7) to bring every term to a sum of prefixed terms and separates two inequivalent normal forms by composing them in parallel with a process built from a name that occurs in neither, which is why $\Delta$ is infinite.

## Depends on

- [Observational equivalence by stratification](../hennessy-milner-logic/observational-equivalence-by-stratification.md)

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>: Section 4.1 (the operator $\mid$, its transition rules and axiom (A7)), Section 4.2 (axioms (A6.1) and (A6.2) and Theorem 4.2) and Appendix C2 (soundness, and completeness, whose steps (A) and (B) use a visible action $\lambda_0$ not occurring in $p$ or $q$).
