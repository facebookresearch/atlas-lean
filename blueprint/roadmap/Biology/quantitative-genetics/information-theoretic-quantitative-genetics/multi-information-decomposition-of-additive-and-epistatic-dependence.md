# Multi-information decomposition of additive and epistatic dependence

Let $X_1, X_2$ be discrete genotype variables at two loci and $X_3$ a discrete phenotype, with Shannon entropies $H_i$, joint entropies $H_{ij}$, $H_{123}$ and mutual informations $I_{ij} = H_i + H_j - H_{ij}$. Define the **multi-information** (total correlation)

$$\Omega = H_1 + H_2 + H_3 - H_{123},$$

and the **differential interaction informations** ("deltas") $\Delta_k = I(X_i; X_j \mid X_k)$ for $\{i,j,k\} = \{1,2,3\}$. Then

$$\Delta_3 = \Omega - I_{13} - I_{23}, \qquad \Delta_2 = \Omega - I_{12} - I_{23}, \qquad \Delta_1 = \Omega - I_{12} - I_{13},$$

and $\Omega \ge I_{ij}$ for every pair (Galas et al. 2021, Proposition 1). The symmetric delta $\bar\Delta = \Delta_1\Delta_2\Delta_3$ measures fully collective dependence.

If the loci segregate independently ($I_{12} = 0$), the total genotype–phenotype dependence splits as $\Omega = (I_{13} + I_{23}) + \Delta_3$, and the fractions

$$F_p = \frac{I_{13} + I_{23}}{\Omega}, \qquad F_e = \frac{\Delta_3}{\Omega} = 1 - F_p$$

quantify the pairwise (additive) and the three-way (epistatic) parts of the dependence. XOR-type genotype–phenotype maps have $I_{13} = I_{23} = 0$ and hence $F_e = 1$: they are invisible to every pairwise test.

## Depends on

- [Mutual information of a finite joint law](../../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)
- [Conditional mutual information of a finite joint law](../../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md)

## Proof depends on

- [Conditional mutual information in terms of entropies](../../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information-eq.md)

## Expansion

Expanding in entropies, $\Omega - I_{13} - I_{23} = H_{13} + H_{23} - H_3 - H_{123}$, which is the definition of $I(X_1; X_2 \mid X_3)$; the other two identities follow by permuting indices. Since conditional mutual information is nonnegative, $\Delta_k \ge 0$, so $\Omega \ge I_{ij} + I_{ik} \ge I_{ij}$. Under $I_{12}=0$ every term in the decomposition is nonnegative, so $F_p, F_e \in [0,1]$.

## Sources

- D. J. Galas, J. Kunert-Graf, L. Uechi and N. A. Sakhanenko, *Toward an information theory of quantitative genetics*, Journal of Computational Biology 28(6) (2021), 527–559, Section on three-variable dependence and Appendix A, Proposition 1. <https://doi.org/10.1089/cmb.2020.0032> (PMCID: PMC8220575)
