# Forking an oracle program at a named query

Let $P$ be an oracle program with explicit coins $s$ that asks queries whose answers lie in a finite set $H$ of size $h$, and finally outputs a pair $(J, y)$ where $J \in \{1, \dots, q\} \cup \{\bot\}$ names one of its queries by position. The *forking algorithm* $\mathrm{Fork}_P$ samples coins $s$ and answers $h_1, \dots, h_q$ uniformly from $H$ and runs $P$; if $P$ outputs $J = \bot$ (or names a position at which no query was asked) it fails. Otherwise it samples fresh answers $h'_J, \dots, h'_q$, reruns $P$ on the same coins with answers $h_1, \dots, h_{J-1}, h'_J, \dots, h'_q$, and succeeds if the rerun names the same position $J$ and $h_J \ne h'_J$, returning both outputs. The *acceptance probability* $\mathrm{acc}$ of $P$ is the probability that a single run names a valid position.

## Depends on

- [Probabilistic oracle program and its semantics against a stateful handler](probabilistic-oracle-program.md)

## Sources

- M. Bellare and G. Neven, "Multi-Signatures in the Plain Public-Key Model and a General Forking Lemma", Proceedings of the 13th ACM Conference on Computer and Communications Security (CCS), 2006.
- D. Pointcheval and J. Stern, "Security Arguments for Digital Signatures and Blind Signatures", Journal of Cryptology 13(3), 2000.
