# Compilation of RC11 to x86-TSO is sound

In the declarative x86-TSO model of Lahav et al., an execution has unmoded reads, writes, fences and single read-modify-write events, a strict total modification order $\mathtt{mo}$ on writes, read-modify-writes and fences, happens-before $\mathtt{hb} = (\mathtt{sb} \cup \mathtt{rf})^+$ and reads-before $\mathtt{rb} = \mathtt{rf}^{-1} ; \mathtt{mo}|_{loc} \setminus [\mathtt{E}]$. It is *TSO-consistent* if it is complete and $\mathtt{hb}$, $\mathtt{mo} ; \mathtt{hb}$, $\mathtt{rb} ; \mathtt{hb}$, $\mathtt{rb} ; \mathtt{mo}$, $\mathtt{rb} ; \mathtt{mo} ; \mathtt{rfe} ; \mathtt{sb}$ (with $\mathtt{rfe} = \mathtt{rf} \setminus \mathtt{sb}$) and $\mathtt{rb} ; \mathtt{mo} ; [\mathtt{RMW} \cup \mathtt{F}] ; \mathtt{sb}$ are irreflexive. Compile reads and non-SC writes to plain loads and stores, SC writes to a store followed by an MFENCE, read-modify-writes to CMPXCHG, SC fences to MFENCE, and other fences to nothing. Then for every program $P$, every outcome of the compiled program under TSO is an [outcome of $P$ under RC11](rc11-program-outcomes.md).

## Depends on

- [Outcomes of a program under RC11](rc11-program-outcomes.md)

## Sources

- O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur and D. Dreyer, "Repairing sequential consistency in C/C++11", *Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2017)*, 2017, <https://plv.mpi-sws.org/scfix/paper.pdf>, Section 4 ("Compilation to x86-TSO"): the TSO executions, Definition 5, the compilation scheme of Figure 8 and Theorem 1.
