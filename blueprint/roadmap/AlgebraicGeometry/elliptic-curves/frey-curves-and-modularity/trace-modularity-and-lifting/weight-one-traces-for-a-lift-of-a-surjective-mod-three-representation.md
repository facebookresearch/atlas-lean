# Weight-one trace realization for an explicit lift of a mod-three representation

Let $\rho:\Gamma_{\mathbb Q}\to\mathrm{GL}_2(\mathbb F_3)$ be continuous and surjective with determinant equal to the mod-three cyclotomic character. Write $A=\mathbb Z[\sqrt{-2}]$ and take the reduction $A\to\mathbb F_3$ sending $\sqrt{-2}$ to $-1$. Suppose given a group homomorphism $\Psi:\mathrm{GL}_2(\mathbb F_3)\to\mathrm{GL}_2(A)$ whose reduction is the identity. Then there exist a nonzero level $N$ and a sequence $b:\mathbb N\to A$ with $b_1=1$ and, for every prime $\ell$ and $n\in\mathbb N$, $b_{\ell n}+e_\ell\mathbf 1_{\ell\mid n}b_{n/\ell}=b_\ell b_n$, where $e_\ell=0$ for $\ell\mid N$ and $e_\ell=\chi_{-3}(\ell)$ otherwise, with $\chi_{-3}$ the quadratic character modulo three. There is an embedding $A\to\mathbb C$ under which $b$ is the full Fourier coefficient sequence of a weight-one cusp form on $\Gamma_1(N)$. Moreover for every prime $q\nmid3N$, every valuation subring of $\overline{\mathbb Q}$ lying over $q$, and every Frobenius at that valuation, $b_q=\mathrm{tr}(\Psi(\rho(\mathrm{Frob}_q)))$ in $A$.

## Expansion

Separate the weight-one realization dictionary, determinant and Frobenius conventions, and the solvable base-change and converse-theorem inputs in the explicit octahedral case. Do not replace the explicit lift assumption by general automorphy.

## Sources

- Anthropic, [LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_LanglandsTunnell_exists_isWeightOneChiNegThreeRealized_eq_trace_lift.lean#L56-L68).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
- [Weight-one realization definition](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_LanglandsTunnell_WeightOneRealizationCarriers.lean).
