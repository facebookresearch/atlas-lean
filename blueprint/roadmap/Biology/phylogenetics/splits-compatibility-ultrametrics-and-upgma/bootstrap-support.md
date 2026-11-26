# Bootstrap support

For a tree estimator $\mathrm{est}$ (a map from alignments of $m$ sites to [unrooted binary phylogenetic trees](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md) on $X$), a taxon $a$, an alignment $M$ of $m$ sites and a set $A$, the bootstrap support of $A$ is

$$\frac{\#\{w : \{1, \dots, m\} \to \{1, \dots, m\} \;:\; A \in \mathcal{C}_a(\mathrm{est}(M \circ w))\}}{m^m},$$

the fraction of the $m^m$ site resamplings with replacement whose estimated tree has $A$ among its clusters seen from $a$ (Felsenstein 1985), with the convention $x/0 = 0$.

## Sources

- J. Felsenstein, *Confidence limits on phylogenies: an approach using the bootstrap*, Evolution 39 (1985), 783–791.
