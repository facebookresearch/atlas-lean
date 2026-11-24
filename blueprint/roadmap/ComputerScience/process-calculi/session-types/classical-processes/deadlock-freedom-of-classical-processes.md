# Deadlock freedom of Classical Processes

In Wadler's calculus of Classical Processes, if $P \vdash \Gamma$ then there is $Q$ with $P \Longrightarrow^* Q$ such that $Q$ is not a top-level cut: every well-typed process can reduce until it is ready to communicate on a free channel. This is the process reading of cut elimination for classical linear logic.

## Depends on

- [Classical Processes and preservation](classical-processes-and-preservation.md)

## Sources

- P. Wadler, "Propositions as sessions", *ICFP 2012*, ACM, 2012, <https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf>, Section 2.7, Theorem 2
- Journal version: P. Wadler, "Propositions as sessions", *Journal of Functional Programming* 24(2–3):384–418, 2014.
