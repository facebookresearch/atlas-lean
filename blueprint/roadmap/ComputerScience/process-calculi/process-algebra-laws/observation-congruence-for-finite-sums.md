# Complete axiomatization of observation congruence for finite sums

Consider the finite terms built from $\mathrm{NIL}$, prefixing $\mu.p$ by $\mu \in M$ and choice $p + q$, with the transitions $\mu.p \xrightarrow{\mu} p$ and $p + q \xrightarrow{\mu} r$ whenever $p \xrightarrow{\mu} r$ or $q \xrightarrow{\mu} r$. Let $M = \Lambda \cup \{\tau\}$, where $\Lambda$ is an infinite set of visible actions and $\tau$ the silent action. For $\lambda \in \Lambda$ write $p \xRightarrow{\lambda} p'$ if $p \xrightarrow{\tau}{}^m \xrightarrow{\lambda} \xrightarrow{\tau}{}^n p'$ for some $m, n \ge 0$. *Weak observational equivalence* $\approx$ is the [stratified observational equivalence](../hennessy-milner-logic/observational-equivalence-by-stratification.md) for the experiment relations $\xRightarrow{\lambda}$, $\lambda \in \Lambda$, and *observational congruence* $\approx_c$ is the largest congruence contained in $\approx$: $p \approx_c q$ if $C[p] \approx C[q]$ for every context $C$.

Then $\approx_c$ on these terms is exactly the congruence induced by the axioms

- (A1) $x + (y + z) = (x + y) + z$, (A2) $x + y = y + x$, (A3) $x + x = x$, (A4) $x + \mathrm{NIL} = x$,
- (A5) $x + \tau x = \tau x$,
- (A6) $\mu(x + \tau y) = \mu(x + y) + \mu y$ for every $\mu \in M$. The completeness proof composes the two terms compared with a process built from a visible action that occurs in neither, so $\Lambda$ must be infinite: if $\Lambda$ is empty, every two terms are weakly equivalent in every context, so $\mathrm{NIL} \approx_c \tau \mathrm{NIL}$, which the axioms do not prove.

Without the silent action, that is with the experiment relations $\xrightarrow{\mu}$ themselves, the congruence is induced by (A1)–(A4) alone.

## Depends on

- [Observational equivalence by stratification](../hennessy-milner-logic/observational-equivalence-by-stratification.md)

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>, Section 3: Theorem 3.1 (the axioms (A1)–(A4) for the strong experiments) and Section 3.3 with Theorem 3.2 (the axioms (A1)–(A6) for the observational congruence $\approx_c$ over $W_{\Sigma_1}$); Figure 1 lists the axioms; Appendix C2, step (B), adds a visible action $\lambda_0$ "not occurring in $p$ or $q$", and Appendix C3 obtains Theorem 3.2 from that proof.
