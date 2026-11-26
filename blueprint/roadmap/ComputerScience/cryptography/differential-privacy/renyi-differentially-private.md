# Rényi differential privacy

A *mechanism* is a map $M : X \to \mathcal{M}(\Omega)$ sending a database $x$ to a measure $M(x)$ on
$\Omega$, the law of the released output (the definition below applies to arbitrary measures). For
a neighbouring relation $\mathrm{Adj}$ on databases and reals $\alpha$ and $\varepsilon$, the
mechanism is *$(\alpha, \varepsilon)$-Rényi differentially private* if

$$
D_\alpha(M(x) \,\|\, M(y)) \le \varepsilon \quad \text{for all } x, y \text{ with } \mathrm{Adj}(x, y),
$$

where $D_\alpha$ is the [Rényi divergence](../../../InformationTheory/information-inequalities/r-nyi-divergence/renyi-div.md)
of order $\alpha$. As for [differential privacy](differentially-private.md), the relation
$\mathrm{Adj}$ is arbitrary. Mironov takes orders $\alpha > 1$. The Rényi divergence is set to
$\infty$ at orders $\alpha \le 1$, so at those orders the condition holds only when no two
databases are neighbours.

## Background

- [Differential privacy](differentially-private.md): the definition that Rényi differential privacy relaxes.

## Sources

- I. Mironov, "Rényi differential privacy", *2017 IEEE 30th Computer Security Foundations Symposium (CSF)*, 263–275, <https://doi.org/10.1109/CSF.2017.11>; numbering of arXiv:1702.07476v3, <https://arxiv.org/abs/1702.07476v3>: Definition 4.
