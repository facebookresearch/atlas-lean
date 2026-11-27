# Greedy partition-entropy selection of informative experiments

**Model.** A signaling pathway is a discrete logical model: variables take states in $\{-1, 0, 1\}$ (deactivated, neutral, activated), zero-indegree variables are *stimulators*, and every other variable's state is a fixed regulation function of its regulators' states. An *experiment* fixes the stimulator states and, optionally, the state of one non-stimulator (knockout $-1$ or over-activation $1$); with $s$ stimulators, $p$ perturbable variables and $k$ perturbation states per variable there are $k^s(pk + 1)$ experiments. A *predicted model state* of an experiment is an assignment consistent with all regulation functions (a logical steady state): there is exactly one for an acyclic model, and possibly zero, one or several for a cyclic one. A *regulatory program* is a regulator together with a regulation function giving the response of a target gene; let $R$ be a set of $r$ programs.

**Distinguishability.** Each predicted model state partitions $R$ by equal predicted response. An experiment $e$ induces the partition $T(e)$, the supremum of the partitions of its predicted model states (the single-block partition if it has none). A list $E = \{e_1, \dots, e_n\}$ induces the meet $S(E) = T(e_1) \wedge \dots \wedge T(e_n)$, and two programs are distinguished by $E$ exactly when they lie in different blocks of $S(E)$. If $S(E)$ has blocks of sizes $n_1, \dots, n_C$, define

$$H(E) = -\sum_{c=1}^{C} \frac{n_c}{r}\log\frac{n_c}{r}, \qquad \mathrm{FUP}(E) = \frac{\sum_{c=1}^C n_c(n_c - 1)}{r(r-1)} .$$

$H$ ranges from $0$ (one block) to $\log r$ (all programs distinguished). FUP is the fraction of the $\binom{r}{2}$ program pairs left undistinguished, from $0$ to $1$.

**Results.**

1. *(Hardness.)* In the relaxed model of the source's Supplementary Information S1, where variables may have any finite number of states and regulatory programs may have several regulators, deciding whether some subset of at most a given size of the candidate experiments distinguishes the same pairs of programs as the full candidate set is NP-complete. (The source's reduction, from 3-dimensional matching, uses Boolean variables and programs with many regulators, so it does not cover the single-regulator three-state model above.)
2. *(Greedy approximation.)* Starting from $E = \emptyset$, repeatedly add the candidate $e$ maximizing the entropy gain $H(E \cup \{e\}) - H(E)$, where $S(E \cup \{e\}) = S(E) \wedge T(e)$. The resulting list has size at most $1 + \ln r + \ln(\log k')$ times the optimum, for cyclic and acyclic models, where $k'$ is the number of states a variable, hence a predicted response, can take ($k' = 3$ here), which bounds the number of blocks of $T(e)$; it is distinct from the perturbation-state count $k$.
3. *(Robustness to multiple steady states.)* If $E$ distinguishes two programs, their predicted response profiles differ under every combination of predicted model states of the experiments in $E$, in particular under the steady states the cell actually reaches.

## Expansion

Selecting experiments that separate all pairs of programs is a set-cover problem over program pairs, which explains the NP-completeness and the logarithmic approximation factor of the greedy rule. Scoring by partition entropy rather than by each experiment alone accounts for redundancy between experiments: a candidate is worth little if it only re-separates pairs already split. Each greedy step makes the partition as uniform as possible. Taking the supremum over a cyclic model's steady states counts only distinctions that hold whichever steady state is realized. Compared with scoring experiments independently, the joint entropy criterion gives lower FUP on randomized versions of the human TNF pathway. On the yeast osmotic-stress and pheromone pathways, the 11 selected experiments identified 26 regulatory modules, 2 of which remained ambiguous.

## Sources

- E. Szczurek, I. Gat-Viks, J. Tiuryn, M. Vingron, "Elucidating regulatory mechanisms downstream of a signaling pathway using informative experiments", Molecular Systems Biology 5 (2009) 287, Results and Materials and methods (sections "Experimental design", "Distinguishing regulatory programs", "The MEED algorithm", "The FUP score"; Propositions 1 and 2 of the Supplementary information), <https://doi.org/10.1038/msb.2009.45>, PMCID: PMC2724975.
