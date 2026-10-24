---
article_id: af_d493cdaf5e7157ffc764a661
declaration: structure
origin: cited
statement: formalized
lean: UniqueGames.UniqueGame
---

# Definition 2.2 (Lecture 16, Section 2.2)

An instance of Unique-Games, denoted by $\Psi$, is composed of a bipartite, bi-regular graph $G = (V = L \cup R, E)$, a finite alphabet $\Sigma$, and a collection of constraints $\Phi = (\phi_e)_{e \in E}$ one for each edge. Each one of the constraints $\phi_e$ is a 1-to-1 map, $\phi_e \colon \Sigma \to \Sigma$. For an edge $e$, the constraint $\phi_e$ defines a collection of tuples which are deemed as satisfactory assignments to the endpoints of the edge, which is $\{(\sigma, \phi_e(\sigma)) \mid \sigma \in \Sigma\}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Lecture 16, Section 2.2](../../../../sources/v1/BooleanFunctions.md)
