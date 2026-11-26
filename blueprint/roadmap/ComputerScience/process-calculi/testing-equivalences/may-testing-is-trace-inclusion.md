# May testing is trace inclusion

Write $A = \Delta \cup \bar\Delta$ for the visible actions. For $s \in A^*$, $p \xRightarrow{s} p'$ means that $p$ reaches $p'$ by performing the actions of $s$ interleaved with finitely many $\tau$-transitions, and $\mathrm{traces}(p) = \{ s \in A^* \mid p \xRightarrow{s} p' \text{ for some } p' \}$. For closed terms $p$ and $q$ of the calculus of [may and must testing](may-and-must-testing-preorders.md),

$$p \sqsubseteq_{\mathrm{may}} q \iff \mathrm{traces}(p) \subseteq \mathrm{traces}(q).$$

Since trace inclusion is preserved by every operator of the calculus, $\sqsubseteq_{\mathrm{may}}$ is a precongruence.

## Depends on

- [May and must testing preorders](may-and-must-testing-preorders.md)

## Sources

- R. De Nicola and M. C. B. Hennessy, "Testing equivalences for processes", *Theoretical Computer Science* 34(1–2):83–133, 1984, <https://www.scss.tcd.ie/Matthew.Hennessy/pubs/old/TCS84.pdf>: Definition 6.4.1 (the alternative preorder $\sqsubseteq'_3$ as trace inclusion), Theorem 6.4.5 for $i = 3$ (proved with the observers $o_s$ that test for the trace $s$), and Theorem 6.4.9 (i).
