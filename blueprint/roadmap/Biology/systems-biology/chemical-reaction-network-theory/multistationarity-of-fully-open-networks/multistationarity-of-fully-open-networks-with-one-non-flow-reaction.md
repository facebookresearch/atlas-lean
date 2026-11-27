# Multistationarity of fully open networks with one non-flow reaction

**Setting.** A chemical reaction network on species $X_1, \dots, X_s$ with mass-action kinetics is **fully open** if it contains the inflow and outflow reactions $0 \rightleftarrows X_i$ for every species (as in a continuous-flow stirred-tank reactor, or a cell with synthesis and degradation of every species). Then the stoichiometric compatibility class is all of $\mathbb{R}^s_{\ge 0}$. The network *admits multistationarity* (MSS) if for some choice of positive rate constants it has at least two positive steady states. A network $N'$ is *embedded* in $N$ if it is obtained by removing some reactions and some species (deleting them from every complex).

**Theorem.**
1. A fully open network whose only non-flow reaction is the irreversible reaction

$$a_1X_1 + \cdots + a_sX_s \ \longrightarrow\ b_1X_1 + \cdots + b_sX_s \qquad (a_i, b_i \ge 0)$$

admits MSS if and only if

$$\sum_{i:\ b_i > a_i} a_i > 1,$$

i.e. the species whose net amount increases are consumed with total molecularity more than one (an autocatalytic reaction of order exceeding one).
2. If the non-flow reaction is reversible, $a\cdot X \rightleftarrows b\cdot X$, the network admits MSS iff $\sum_{i: b_i > a_i} a_i > 1$ or $\sum_{i: a_i > b_i} b_i > 1$.

In both cases the multistationary networks admit nondegenerate steady states.

**Atoms of multistationarity.** A one-reaction fully open network is a minimal multistationary network with respect to the embedding order (a CFSTR atom of multistationarity) if and only if its non-flow reaction is irreversible and of one of the two forms

$$a_1X \to a_2X \ \ (a_2 > a_1 > 1), \qquad X + Y \to b_1X + b_2Y \ \ (b_1 > 1,\ b_2 > 1).$$

A one-reaction fully open network has such an atom as an embedded network iff it admits nondegenerate MSS. Consequently, any fully open network, with any number of non-flow reactions, that contains one of these two reactions as an embedded network admits MSS.

## Expansion

With one non-flow reaction of rate $\kappa x^{a}$, steady states satisfy $x_i = c_i + (b_i - a_i)\,\kappa x^a/k_i$ for flow constants, so each $x_i$ is an affine function of the single reaction flux $\xi = \kappa x^a$; MSS reduces to the scalar equation $\xi = \kappa\prod_i (c_i + d_i\xi)^{a_i}$ with $d_i = (b_i - a_i)/k_i$ having multiple positive roots. Factors with $d_i > 0$ make the right side convex and growing with total degree $\sum_{b_i > a_i}a_i$, so a line can cross it twice exactly when that degree exceeds one; factors with $d_i < 0$ only bound the range. Nondegenerate MSS lifts from an embedded network to the larger one (Joshi–Shiu), which gives the sufficient criterion for large networks; the condition identifies multistationarity with genuine autocatalysis.

## Sources

- Badal Joshi, "Complete characterization by multistationarity of fully open networks with one non-flow reaction", Applied Mathematics and Computation 219 (2013), 6931–6945, <https://doi.org/10.1016/j.amc.2013.01.027>; numbering as in arXiv:1207.6018: Theorems 4.1, 4.13 and 4.14.
