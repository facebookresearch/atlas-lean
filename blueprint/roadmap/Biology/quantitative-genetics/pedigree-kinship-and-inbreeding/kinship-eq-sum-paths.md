# Wright's path formula for kinship

Let a [pedigree](pedigree.md) have [no selfing](no-selfing.md). Then for all individuals $i, j$,

$$\varphi_{ij} = \sum_{A} \sum_{p \in \Pi(i, A)} \sum_{p' \in \Pi(j, A)} \Bigl(\frac12\Bigr)^{|p| + |p'| - 1} \bigl(1 + F^{\mathrm{tab}}_A\bigr)\, [\,p \cap p' = \{A\}\,],$$

where $\varphi$ is the [tabular kinship](kinship.md), $A$ ranges over all individuals, $\Pi(i, A)$ is the set of [ancestral paths from $i$ to $A$](paths-to.md), $|p|$ the number of individuals on $p$, $F^{\mathrm{tab}}$ the [tabular inbreeding coefficient](kinship-inbreeding.md), and the indicator requires that every individual on both $p$ and $p'$ be $A$. Here $|p| + |p'| - 1$ is the number of individuals on the loop through $A$.
