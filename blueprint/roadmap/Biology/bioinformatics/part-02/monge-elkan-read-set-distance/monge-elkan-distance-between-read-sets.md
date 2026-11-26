# Monge–Elkan distance between read sets

**Setting.** Two unknown sequences $A,B$ are observed only through read sets $R_A=\{a_1,\dots,a_m\}$ and $R_B=\{b_1,\dots,b_n\}$ of reads of length $l$ sampled at random positions (coverage $\alpha$, so $|A|=\tfrac{l}{\alpha}|R_A|$). Let $d$ be the Levenshtein distance on reads. The goal is to approximate $d(A,B)$ without assembling $A$ and $B$.

**Definition (Monge–Elkan read-set distances).** The directed Monge–Elkan distance matches each read with its closest read in the other set and averages:

$$
D_{\mathrm{ME}}(R_A,R_B)=\frac1{|R_A|}\sum_{a\in R_A}\min_{b\in R_B} d(a,b).
$$

Its symmetrization and scale correction are

$$
D_{\mathrm{MES}}(R_A,R_B)=\tfrac12\big(D_{\mathrm{ME}}(R_A,R_B)+D_{\mathrm{ME}}(R_B,R_A)\big),\qquad
D_{\mathrm{MESS}}(R_A,R_B)=\max\{|R_A|,|R_B|\}\,D_{\mathrm{MES}}(R_A,R_B).
$$

When strand or read orientation is unknown, $d(a,b)$ is replaced by the minimum over the admissible versions $b,\ \bar b,\ b^{R},\ \bar b^{R}$ (complement, reverse, reverse complement). A margin-gap variant forgives leading or trailing gaps of length below $t<l/2$ in each read alignment.

**Properties.**

1. $D_{\mathrm{ME}}$ is not symmetric in general; $D_{\mathrm{MES}}$ is symmetric and vanishes when every read of each set has an exact copy in the other.
2. Since $d(a,b)\le l$ for reads of length $l$, $D_{\mathrm{MES}}\le l$, whereas $d(A,B)\le\max\{|A|,|B|\}$. The factor $\max\{|A|,|B|\}/l=\max\{|R_A|,|R_B|\}/\alpha$ puts the two on the same scale; dropping the constant $\alpha$ gives $D_{\mathrm{MESS}}$. This corrects the defect that $D_{\mathrm{MES}}(R_{AA},R_B)=D_{\mathrm{MES}}(R_A,R_B)$ when $A$ is duplicated into $AA$.
3. Computing $D_{\mathrm{ME}}$ needs at most $|R_A||R_B|$ read alignments, avoiding the NP-hard assembly step; the inner minimum can be restricted to candidates pre-selected by the $q$-gram lower bound.

## Expansion

The heuristic premise is that the read of $R_B$ nearest to $a\in R_A$ comes from the homologous position of $B$, so the minimum isolates the local divergence at that position; averaging over reads then estimates the per-read divergence, and scaling by sequence length (estimated by read count) turns it into an estimate of the global edit distance. At low coverage this estimate is closer to the true $d(A,B)$ than assembling contigs and comparing them, and it yields better hierarchical clusterings of sequences.

## Depends on

- [q-gram lower bound on edit distance](q-gram-lower-bound-on-edit-distance.md)

## Sources

- Petr Ryšavý, Filip Železný, "Estimating Sequence Similarity from Read Sets for Clustering Next-Generation Sequencing data", arXiv:1705.06125 (2017), Section 3 (Monge–Elkan distance, strand and orientation, distance scale, margin gaps), <https://doi.org/10.48550/arXiv.1705.06125>.
- A. E. Monge, C. P. Elkan, "The field matching problem: algorithms and applications", *Proc. KDD* (1996).
