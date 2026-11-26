# Smooth calibration error and interval calibration error

For a distribution $\Gamma$ of pairs $(v, y) \in [0,1] \times \{0,1\}$, the **smooth calibration error** is

$$
\mathrm{smCE}(\Gamma) = \sup_{w} \mathbb{E}_{(v,y) \sim \Gamma}\big[w(v)\,(y - v)\big],
$$

the supremum over all $1$-Lipschitz functions $w : [0,1] \to [-1,1]$. The **interval calibration error** $\mathrm{intCE}(\Gamma)$ is the infimum, over partitions of $[0,1]$ into intervals, of the binned calibration error plus the width-weighted cost of the partition, as defined by Błasiok, Gopalan, Hu and Nakkiran. A calibration measure $\mu$ is **$(c,s)$-consistent** if it satisfies robust completeness $\mu \le a\,\mathrm{dCE}^c$ and robust soundness $\mu \ge b\,\mathrm{dCE}^s$ for constants $a, b > 0$ and all distributions and predictors.

## Depends on

- [Distance to calibration and its upper and lower variants](distance-to-calibration.md)

## Sources

- J. Blasiok, P. Gopalan, L. Hu, P. Nakkiran, "A Unifying Theory of Distance from Calibration", STOC (2023), arXiv:2211.16886.
