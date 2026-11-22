# Wright's path formula for the inbreeding coefficient

Let a [pedigree](pedigree.md) have [no selfing](no-selfing.md) (distinct parents for every non-founder), and let $i$ have parents $f = f(i)$ and $m = m(i)$. Then

$$F_i = \sum_{A} \sum_{p \in \Pi(f, A)} \sum_{p' \in \Pi(m, A)} \Bigl(\frac12\Bigr)^{|p| + |p'| - 1} (1 + F_A)\, [\,p \cap p' = \{A\}\,],$$

where $F$ is the gene-dropping [inbreeding coefficient](inbreeding.md), $A$ ranges over all individuals (common ancestors of $f$ and $m$, including $f$ or $m$ themselves, contribute), $\Pi(x, A)$ is the set of [ancestral paths from $x$ to $A$](paths-to.md), $|p|$ the number of individuals on $p$, and the indicator requires that $p$ and $p'$ share no individual other than $A$ (Wright 1922).

## Sources

- S. Wright, *Coefficients of inbreeding and relationship*, Am. Nat. 56 (1922), 330–338.
