# NP-hardness of the de Bruijn superwalk with multiplicities problem

Given a de Bruijn graph of order $k$ over an alphabet $\Sigma$, a multiplicity $m(e) \in \mathbb{Z}_{\ge 0}$ for every edge $e$, and a set of walks (the reads), the **de Bruijn Superwalk with Multiplicities** (DBSM) problem asks whether there is a walk that traverses every edge $e$ exactly $m(e)$ times and contains every read as a subwalk.

**Theorem.** DBSM is NP-hard for every fixed $|\Sigma| \ge 2$ and every positive integer $k$ (Kapun and Tsarev 2013, Theorem 2).

Together with the NP-hardness of the shortest common superstring and de Bruijn shortest superwalk formulations, this shows that all the standard error-free combinatorial models of genome assembly are NP-hard; the special case where every read is a single edge remains polynomial (Eulerian walk).

## Depends on

- [NP-hardness of common superstring with multiplicities](np-hardness-of-common-superstring-with-multiplicities.md)

## Expansion

Take a graph with one vertex and two loops labelled $0$ and $1$. A binary CSM instance becomes a DBSM instance on this graph by reading each string as a walk and setting the multiplicities of the two loops to $l_0$ and $l_1$; a solution walk is then exactly a superstring with the prescribed letter counts. This two-loop graph embeds in a de Bruijn graph of any order $k$: loop $0$ maps to a self-loop and loop $1$ to a cycle of length $k+1$.

## Sources

- E. Kapun and F. Tsarev, *De Bruijn superwalk with multiplicities problem is NP-hard*, BMC Bioinformatics 14 (Suppl 5) (2013), S7, Theorem 2. <https://doi.org/10.1186/1471-2105-14-S5-S7> (PMCID: PMC3622630)
