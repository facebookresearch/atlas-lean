---
article_id: af_93f9f96c467f2f9dd4560818
declaration: structure
origin: cited
statement: formalized
lean: UniqueGames.UniqueGame
---

# Definition 3.5 (Lecture 15, Section 3.2)

An instance of Unique-Games, denoted by $\Psi$, is composed of a bipartite, bi-regular graph $G = (V = L \cup R, E)$, a finite alphabet $\Sigma$, and a collection of constraints $\Phi = (\phi_e)_{e \in E}$ one for each edge. Each one of the constraints $\phi_e$ is a 1-to-1 map, $\phi_e \colon \Sigma \to \Sigma$. For an edge $e$, the constraint $\phi_e$ defines a collection of tuples which are deemed as satisfactory assignments to the endpoints of the edge, which is $\{(\sigma, \phi_e(\sigma)) \mid \sigma \in \Sigma\}$. The goal in Unique-Games is to find an assignment $A \colon V \to \Sigma$ that satisfies as many of the constraints $\phi_e$. The value of a Unique-Games instance, denoted by $\operatorname{val}(\Psi)$, is defined to be $\max_{A \colon V \to \Sigma} \frac{\#\{e \mid A \text{ satisfies } \phi_e\}}{|E|}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Lecture 15, Section 3.2](../../../../sources/v1/BooleanFunctions.md)
