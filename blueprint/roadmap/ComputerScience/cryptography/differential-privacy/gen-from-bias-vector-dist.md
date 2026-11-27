# Generation from a bias-vector distribution

The generator that draws a bias vector $p$
from `biasDist`, then a codebook whose entries are independent with $\Pr[c_{ij} = 1] = p_j$, and
returns the codebook with $p$ as the key.
