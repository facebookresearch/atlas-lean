# Quantitative quartet gap under the DLCoal model

**Model.** In the DLCoal model on a rooted species tree $T$ (edge lengths in coalescent units, depth $\Delta$, minimum branch length $f$), a locus tree grows top-down: each gene copy duplicates at rate $\lambda$ and is lost at rate $\mu$ ($\lambda\ne\mu$), with one daughter edge per duplication, and every surviving copy bifurcates at speciations. Gene trees then arise by a Kingman coalescent inside the locus tree, conditioned so that lineages at the bottom of a daughter edge coalesce below its top. Gene trees are multi-labelled (several copies per species).

**Quartet events.** Fix species $A,B,C,D$ with species quartet $AB|CD$. Condition on the copy numbers $\mathcal X=(\mathcal A,\mathcal B,\mathcal C,\mathcal D)\ge\vec 1$ and on the number $I\ge1$ of locus copies leaving the most recent common ancestor $R$ of the quartet (measure $\mathbb P''$). Pick one copy $a,b,c,d$ per species uniformly at random, let $i_x$ be the ancestral lineage of $x$ at $R$, and let $Q_1,Q_2,Q_3$ be the events that the gene quartet is $ab|cd$, $ac|bd$, $ad|bc$. Put $x=\mathbb P''[i_a=i_b]$, $y=\mathbb P''[i_c=i_d]$.

**Proposition (balanced quartet).** If the root of $T^{\{A,B,C,D\}}$ lies on the internal edge, then almost surely $x\wedge y\ge 1/I$ and

$$\mathbb P''[Q_1]-\mathbb P''[Q_2]>\tfrac1{12}\Big(\big(x-\tfrac1I\big)\wedge\big(y-\tfrac1I\big)\Big).$$

**Proposition (caterpillar quartet).** If the root lies on the pendant edge of $D$, then almost surely $x\ge 1/I$ and

$$\mathbb P''[Q_1]-\mathbb P''[Q_2]>\tfrac13\big(x-\tfrac1I\big).$$

**Branching-process bounds.** Let $\sigma=\min_{\mathcal Q}\mathbb P[\mathcal X_{\mathcal Q}\ge\vec 1]$ (worst quartet survival probability) and $\alpha=\max_R\mathbb E[I_R]$. Then $\sigma\ge\big[e^{-(\mu-\lambda)\Delta}(1-\lambda/\mu)\big]^4$ if $\mu>\lambda$, $\sigma\ge(1-\mu/\lambda)^4$ if $\lambda>\mu$, and $\alpha\le 1\vee e^{(\lambda-\mu)\Delta}$. With $\gamma=1-e^{-f}$ and $\delta'=\mathbb P'[Q_1]-\tfrac13$ under conditioning on $\mathcal X\ge\vec1$ only,

$$\delta'\ \ge\ \tfrac23\Big\{\gamma\wedge\tfrac18\Big\}\frac{\sigma^3}{\alpha^3}.$$

## Expansion

Decompose by which pairs of sampled copies descend from the same locus lineage at $R$ and by whether the lineages coalesce on the internal branch. Without coalescence on that branch the locus structure alone favors $Q_1$ by explicit symmetry identities, and coalescence of $a,b$ (or $c,d$) only increases $\mathbb P''[Q_1]$; the probabilities of the copy-sharing events are explicit functions of $I$, $x$, $y$, which yields the stated gaps. Integrating, the event that the sampled pair has coalesced on the internal edge has conditional probability at least $(\gamma\wedge\frac18)/I$, so the gap is at least of order $\mathbb E'[I^{-3}]$, and Jensen's inequality with $\mathbb E[I]\ge\sigma\,\mathbb E'[I]$ gives the bound on $\delta'$. The survival bound uses the birth-death extinction function along root-to-leaf paths.

## Sources

- M. Hill, B. Legried, S. Roch, "Species tree estimation under joint modeling of coalescence and duplication: sample complexity of quartet methods", arXiv:2007.06697 (2020), <https://doi.org/10.48550/arXiv.2007.06697>. Section 3 (Propositions 1 and 2; Lemmas 1–12) and Section 4 (Lemmas 13, 14, 16, 17).
