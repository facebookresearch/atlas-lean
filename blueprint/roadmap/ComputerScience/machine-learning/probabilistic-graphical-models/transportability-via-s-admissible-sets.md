# Transportability via S-admissible sets

Let $D$ be a selection diagram for a source population $\Pi$ and a target population $\Pi^*$: a causal
diagram over the observed variables augmented with selection nodes $S$ pointing to the variables whose
mechanisms may differ between the populations. Let $X$, $Y$, $Z$ be disjoint sets of observed variables,
with $Z$ containing no descendant of $X$, and suppose $Z$ is S-admissible: $Y$ is d-separated from $S$ by
$X \cup Z$ in the diagram with all arrows into $X$ removed. If $P(y \mid \mathrm{do}(x), z)$ is available from
the source and $P^*(z) > 0$ implies that this conditional is defined, then

$$P^*(y \mid \mathrm{do}(x)) = \sum_z P(y \mid \mathrm{do}(x), z)\, P^*(z).$$

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: selection diagrams for a pair of populations.

## Depends on

- [d-separation](causal-bayesian-networks/dseparated.md)

## Proof depends on

- [Rule 1 of the do-calculus](causal-bayesian-networks/do-calculus-rule1.md)
- [Rule 3 of the do-calculus](causal-bayesian-networks/do-calculus-rule3.md)

## Sources

- J. Pearl and E. Bareinboim, *Transportability of causal and statistical relations: a formal approach*, AAAI 2011 (technical report R-372): Definition 4 (S-admissibility), Theorem 1 and Corollary 1, which gives this transport formula for an S-admissible set of pre-treatment covariates. <https://ftp.cs.ucla.edu/pub/stat_ser/r372.pdf>
- J. Pearl, *The do-calculus revisited*, UAI 2012, Section 3: selection diagrams, Definition 4 (transportability) and Theorem 1 (transportability by reduction with the do-calculus). With $Z$ S-admissible, rule 1 removes $S$ from $P(y \mid \mathrm{do}(x), z, s)$; with $Z$ free of descendants of $X$, rule 3 gives $P^*(z \mid \mathrm{do}(x)) = P^*(z)$. <https://arxiv.org/pdf/1210.4852>
