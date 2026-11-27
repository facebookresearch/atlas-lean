# Probing-weighted ensemble reduces expected distance to footprinting data

**Setting.** Fix an RNA sequence, normalized footprinting data $q$, and an additive distance $d(S,q) = \sum_i \delta_i(s_i) \ge 0$ between the pairing pattern of a secondary structure $S$ and $q$, as in the [probing-weighted partition function](probing-weighted-partition-function-of-rna-secondary-structures.md). For $\beta \ge 0$ let

$$P_\beta(S) = \frac{e^{-E(S)/RT}\,e^{-\beta d(S,q)}}{Z_\beta}, \qquad D_\beta = \sum_S P_\beta(S)\, d(S,q),$$

so $P_0$ is the Boltzmann distribution and $D_0$ the expected distance of the unweighted low-energy ensemble from the data.

**Critical distance.** For $\beta>0$ put $d_0 = \beta^{-1}\ln(Z_0/Z_\beta)$. Then for every structure $S$,

$$P_\beta(S) > P_0(S) \iff d(S,q) < d_0, \qquad P_\beta(S) < P_0(S) \iff d(S,q) > d_0 .$$

**Theorem.**

1. $D_\beta \le D_0$ for every $\beta > 0$.
2. More generally, $\beta \mapsto D_\beta$ is nonincreasing on $[0,\infty)$, strictly decreasing unless $d(\cdot,q)$ is constant on all secondary structures; in fact $\frac{d}{d\beta}D_\beta = -\operatorname{Var}_{P_\beta}\bigl(d(S,q)\bigr)$.

**Quadratic-time evaluation.** Since $d$ is a sum over positions,

$$D_\beta = \sum_{i=1}^{n}\Bigl[\pi_i\,\delta_i(\text{paired}) + (1-\pi_i)\,\delta_i(\text{unpaired})\Bigr], \qquad \pi_i = \sum_{j} P_\beta(i,j),$$

so $D_\beta$ is obtained in $O(n^2)$ time from the base-pair probability matrix, without enumerating or sampling structures.

## Expansion

The critical distance follows from $P_\beta(S)/P_0(S) = e^{-\beta d(S,q)}Z_0/Z_\beta$. Sort structures by distance: reweighting moves probability mass from structures farther than $d_0$ to structures closer than $d_0$, and since both distributions have total mass one, the mean distance cannot increase; this is the argument of the paper's Theorem 1. The monotonicity in $\beta$ is the general fact that exponential tilting $P_\beta \propto P_0\,e^{-\beta d}$ decreases the mean of $d$: $\ln Z_\beta$ is convex in $\beta$ with $\frac{d}{d\beta}\ln Z_\beta = -D_\beta$ and second derivative $\operatorname{Var}_{P_\beta}(d)$. The guarantee is about agreement with the probing data, not about accuracy against the native structure, which depends on the quality of the data and of $\beta$.

## Depends on

- [Probing-weighted partition function of RNA secondary structures](probing-weighted-partition-function-of-rna-secondary-structures.md)

## Sources

- K. Zarringhalam, M. M. Meyer, I. Dotu, J. H. Chuang, P. Clote, "Integrating chemical footprinting data into RNA secondary structure prediction", PLoS One (2012), Methods: "RNAsc is guaranteed to improve agreement with shape data" (Eqs. (9)–(18), Theorems 1–2) and quadratic-time computation of expected distance (Eqs. (19)–(21)), <https://doi.org/10.1371/journal.pone.0045160>, PMCID PMC3473038.
