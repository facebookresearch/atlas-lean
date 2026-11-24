# Hadamard conjugation for group-based models

Let $T$ be a phylogenetic tree with leaves $0, 1, \dots, n$ in which each edge $e$ carries Kimura three-substitution-type (K3ST) parameters $q_e(\alpha), q_e(\beta), q_e(\gamma)$, the substitutions forming the Klein group $\mathbb{Z}_2 \times \mathbb{Z}_2$. Index rows and columns of $2^n \times 2^n$ matrices by subsets of $[n] = \{1, \dots, n\}$. The edge-length spectrum $Q_T$ has, for each edge $e_C$ inducing the split with part $C \subseteq [n]$, entries $Q_{\emptyset, C} = q_{e_C}(\alpha)$, $Q_{C, \emptyset} = q_{e_C}(\beta)$, $Q_{C, C} = q_{e_C}(\gamma)$, the entry $Q_{\emptyset,\emptyset} = -K$ with $K$ the sum of all edge parameters, and zeros elsewhere; the sequence probability spectrum $P_T$ has entry $p_{A,B}$, the probability of the site pattern coded by $(A, B)$. Let $H_n$ be the Sylvester Hadamard matrix of order $2^n$, so $H_n^{-1} = 2^{-n}H_n$. Hendy and Snir (2005, Theorem 7, equations (8) and (9)) prove that $P_T$ is determined by $Q_T$ through an entrywise exponential after Hadamard conjugation, and that $Q_T$ is recovered from $P_T$ by the entrywise logarithm when its arguments are positive; written in the form used in their proof and in their equation (9),
$$H_nP_TH_n = \mathrm{Exp}(H_nQ_TH_n), \qquad Q_T = H_n^{-1}\,\mathrm{Ln}(H_nP_TH_n)\,H_n^{-1}.$$
Hence the tree (the support of $Q_T$) and all edge parameters are recovered from the expected pattern frequencies. This is the invertible relationship between a tree with K3ST edge parameters and the expected nucleotide pattern frequencies reported by Hendy, Penny and Steel (1994), extending the transform for the two-state Cavender–Farris model.

## Expansion

1. The K3ST model, the Klein-group structure of the substitutions (Observation 1), and the diagonalization of the one-edge transition matrix by the $4 \times 4$ Hadamard matrix (Observation 2 and equations (2)–(3)).
2. The coding of site patterns by pairs of subsets $(A, B)$ of $[n]$ and the sparse edge-length spectrum.
3. Pathsets and the interpretation of the entries of $H_nQ_TH_n$ and $H_nP_TH_n$ through pathset distances.
4. Theorem 7 in the form $H_nP_TH_n = \mathrm{Exp}(H_nQ_TH_n)$, which matches the source's equation (9) and the entrywise computation of $[\mathrm{Exp}(H_nQ_TH_n)]_{A,B}$ in its proof, and the inverse under the positivity condition.
5. The two-state Cavender–Farris case and the vector form with $4^n$ components used by Hendy, Penny and Steel.

## Sources

- M. D. Hendy and S. Snir, Hadamard conjugation for the Kimura 3ST model: combinatorial proof using pathsets, arXiv:q-bio/0505055v2 (2005), Sections 2–5, Theorem 7. <https://arxiv.org/abs/q-bio/0505055>
- M. D. Hendy, D. Penny and M. A. Steel, A discrete Fourier analysis for evolutionary trees, Proc. Natl. Acad. Sci. USA 91 (1994), 3339–3343, abstract. <https://doi.org/10.1073/pnas.91.8.3339>
