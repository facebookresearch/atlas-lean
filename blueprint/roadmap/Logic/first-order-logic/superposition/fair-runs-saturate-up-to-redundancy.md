# Fair superposition runs saturate up to redundancy

If a run $N_0 \vdash N_1 \vdash \cdots$ of the superposition calculus is [fair](redundancy-and-fair-runs-for-superposition.md), then its limit $N_\infty$ is saturated up to redundancy. Moreover $N_i \subseteq N_\infty \cup \mathrm{Red}(N_\infty)$ for every $i$.

**Proof.** Redundancy is monotone, $N \subseteq N'$ implies $\mathrm{Red}(N) \subseteq \mathrm{Red}(N')$, and deleting redundant clauses keeps redundancy, $N' \subseteq \mathrm{Red}(N)$ implies $\mathrm{Red}(N) \subseteq \mathrm{Red}(N \setminus N')$; hence $\mathrm{Red}(N_i) \subseteq \mathrm{Red}(N_\infty)$, and a clause deleted at step $k$ is redundant with respect to $N_{k+1}$ and so with respect to $N_\infty$. By fairness the conclusion of every inference from non-redundant persistent clauses lies in some $N_i \cup \mathrm{Red}(N_i) \subseteq N_\infty \cup \mathrm{Red}(N_\infty)$.

## Depends on

- [Redundancy and fair runs for superposition](redundancy-and-fair-runs-for-superposition.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.4, Lemmas 3.12–3.14, Corollary 3.15 and Lemma 3.16 with their proofs, pp. 60–61.
