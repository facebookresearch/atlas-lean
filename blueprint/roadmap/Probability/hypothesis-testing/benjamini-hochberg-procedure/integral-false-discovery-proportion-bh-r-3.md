# Benjamini–Yekutieli FDR control under arbitrary dependence

Let $p_1, \dots, p_m$ be measurable p-values, let $H_0 \subseteq \{1, \dots, m\}$ be the set of true null
hypotheses, and let every true-null p-value be valid: $\Pr[p_i \le t] \le t$ for $i \in H_0$ and
$t \in [0, 1]$. Then for $q \in [0, 1]$ the Benjamini–Hochberg procedure run at the corrected level
$q/H_m$, where $H_m = \sum_{k=1}^m 1/k$, has false discovery rate at most $q|H_0|/m$, with no assumption
on the joint law of the p-values: they may be arbitrarily dependent. The factor $H_m \approx \log m$ is
the price of dropping independence. For $m = 0$ both sides are $0$.

## Sources

- Benjamini and Yekutieli, *The control of the false discovery rate in multiple testing under
  dependency*, Ann. Statist. 29 (2001), 1165–1188, Theorem 1.3.
