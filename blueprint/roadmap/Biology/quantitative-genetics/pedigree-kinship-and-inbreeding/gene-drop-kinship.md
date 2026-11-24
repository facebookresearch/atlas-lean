# Kinship coefficient under gene dropping

In a [pedigree](pedigree.md), the gene-dropping kinship of individuals $i$ and $j$ is

$$\varphi^{\mathrm{gd}}_{ij} = \frac{1}{4} \sum_{a, b \in \{0, 1\}} \mathrm{IBD}\bigl((i, a), (j, b)\bigr),$$

where $\mathrm{IBD}$ is the [probability of identity by descent](ibd.md): the probability that a copy drawn at random from $i$ and one drawn at random from $j$ are identical by descent.
