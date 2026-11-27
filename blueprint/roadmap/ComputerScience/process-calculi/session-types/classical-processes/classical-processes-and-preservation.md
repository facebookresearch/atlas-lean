# Classical Processes and preservation

In Wadler's calculus CP of Classical Processes, a process $P$ is typed by a sequent $P \vdash \Gamma$ of classical linear logic, where the environment $\Gamma$ assigns propositions (session types) to distinct channel names, and dual propositions describe the two ends of a channel. Cut is parallel composition with restriction of the cut channel, $\nu x.(P \mid Q)$. Reduction $\Longrightarrow$ consists of the principal reductions, which eliminate a cut between dual logical rules acting on the cut channel, the commuting conversions, which move a cut past a logical rule acting on another channel, and the axiom cut, closed under structural equivalence and under reduction inside either side of a cut; there is no reduction under other operators. Reduction preserves typing (subject reduction): if $P \vdash \Gamma$ and $P \Longrightarrow Q$ then $Q \vdash \Gamma$.

## Sources

- P. Wadler, "Propositions as sessions", *ICFP 2012*, ACM, 2012, <https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf>, Sections 2.1–2.7 (Figures 2–4) and Theorem 1
- Journal version: P. Wadler, "Propositions as sessions", *Journal of Functional Programming* 24(2–3):384–418, 2014.
