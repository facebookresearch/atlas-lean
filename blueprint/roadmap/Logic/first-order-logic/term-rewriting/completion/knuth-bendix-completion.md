# Knuth–Bendix completion

Fix a [reduction ordering](../reduction-ordering.md) $\succ$. Completion works on pairs $(E, R)$ of a set $E$ of equations and a set $R$ of rewrite rules, which need not be finite (an implementation started on finite input keeps them finite); $s \doteq t$ stands for $s \approx t$ or $t \approx s$, and $\mathrm{CP}(R)$ is the set of [critical pairs](../../automated-deduction/critical-pairs-of-a-term-rewriting-system.md) of $R$. The *encompassment* quasi-ordering is $s \sqsupseteq l$ if $s|_p = l\sigma$ for some position $p$ and substitution $\sigma$, with strict part $\sqsupset$. The inference rules $E, R \vdash E', R'$ are:

- **Orient:** $E \cup \{s \doteq t\}, R \vdash E, R \cup \{s \to t\}$ if $s \succ t$;
- **Delete:** $E \cup \{s \approx s\}, R \vdash E, R$;
- **Deduce:** $E, R \vdash E \cup \{s \approx t\}, R$ if $\langle s, t \rangle \in \mathrm{CP}(R)$;
- **Simplify-Eq:** $E \cup \{s \doteq t\}, R \vdash E \cup \{u \approx t\}, R$ if $s \to_R u$;
- **R-Simplify-Rule:** $E, R \cup \{s \to t\} \vdash E, R \cup \{s \to u\}$ if $t \to_R u$;
- **L-Simplify-Rule:** $E, R \cup \{s \to t\} \vdash E \cup \{u \approx t\}, R$ if $s \to_R u$ using a rule $l \to r \in R$ with $s \sqsupset l$.

A *run* with input $E_0$ and $\succ$ is a finite or infinite sequence $E_0, R_0 \vdash E_1, R_1 \vdash \cdots$ with $R_0 = \emptyset$. Its unions are $E_\infty = \bigcup_i E_i$ and $R_\infty = \bigcup_i R_i$, and its *persistent* equations and rules are $E_* = \bigcup_i \bigcap_{j \ge i} E_j$ and $R_* = \bigcup_i \bigcap_{j \ge i} R_j$ (for a finite run ending in $E_n, R_n$ these are $E_n$ and $R_n$). A run is *fair* if $\mathrm{CP}(R_*) \subseteq E_\infty$.

## Depends on

- [Reduction ordering](../reduction-ordering.md)
- [Critical pairs of a term rewriting system](../../automated-deduction/critical-pairs-of-a-term-rewriting-system.md)
- [Equational consequence and E-algebras](../../equational-logic/equational-consequence-and-e-algebras.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.6, pp. 122–125: inference rules, the encompassment ordering, runs, persistent sets and fairness.
