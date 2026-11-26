# Characterization of the must testing preorder

Write $A = \Delta \cup \bar\Delta$ for the visible actions. For $s \in A^*$, $p \xRightarrow{s} p'$ means that $p$ reaches $p'$ by performing the actions of $s$ interleaved with finitely many $\tau$-transitions, and $\mathrm{traces}(p) = \{ s \in A^* \mid p \xRightarrow{s} p' \text{ for some } p' \}$. A closed term $p$ *diverges* if some computation from $p$ (a maximal sequence of $\tau$-transitions) is infinite or contains a term that does not converge; $p \Downarrow$ means that $p$ does not diverge. For $s \in A^*$ define $p \Downarrow s$ by $p \Downarrow \varepsilon$ if $p \Downarrow$, and $p \Downarrow \alpha s$ if $p \Downarrow$ and $p' \Downarrow s$ whenever $p \xRightarrow{\alpha} p'$. Let $p \text{ after } \varepsilon = \{ p \}$ and, for $\alpha \in A$ and $s \in A^*$, $p \text{ after } \alpha s = \bigcup \{ p' \text{ after } s \mid p \xRightarrow{\alpha} p' \}$; for a set $P$ of terms, $P \text{ after } s = \bigcup_{p \in P} p \text{ after } s$. For a finite $L \subseteq A$, a set $P$ of terms *must* $L$ if for every $p \in P$ and every $p'$ with $p \xRightarrow{\varepsilon} p'$ there are $\lambda \in L$ and $p''$ with $p' \xRightarrow{\lambda} p''$.

Then for closed terms $p$ and $q$ of the calculus of [may and must testing](may-and-must-testing-preorders.md), $p \sqsubseteq_{\mathrm{must}} q$ if and only if for every $s \in A^*$ and every finite $L \subseteq A$, $p \Downarrow s$ implies

1. $q \Downarrow s$, and
2. if $p \text{ after } s$ must $L$, then $q \text{ after } s$ must $L$.

## Depends on

- [May and must testing preorders](may-and-must-testing-preorders.md)

## Sources

- R. De Nicola and M. C. B. Hennessy, "Testing equivalences for processes", *Theoretical Computer Science* 34(1–2):83–133, 1984, <https://www.scss.tcd.ie/Matthew.Hennessy/pubs/old/TCS84.pdf>: the notions $\Downarrow s$, $\text{after}$ and $\text{must}$ of Section 6.2, Definition 6.4.1 (the preorder $\sqsubseteq'_2$), Lemmas 6.4.2–6.4.4 and Theorem 6.4.5 for $i = 2$.
