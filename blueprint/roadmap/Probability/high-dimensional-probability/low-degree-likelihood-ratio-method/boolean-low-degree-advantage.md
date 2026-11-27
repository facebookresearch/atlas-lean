# Low-degree advantage for planted problems over the hypercube

If the null distribution $\mathbb{Q}$ is uniform on $\{\pm 1\}^N$ and $\mathbb{P}$ is any distribution on $\{\pm1\}^N$, then with characters $\chi_S(y) = \prod_{i \in S} y_i$,

$$
\|L^{\le D}\|^2 = \sum_{S \subseteq [N],\, |S| \le D} \big(\mathbb{E}_{\mathbb{P}}[\chi_S]\big)^2 .
$$

For a planted model in which $\mathbb{P}$ draws a hidden structure $u$ and then $y$ from $P_u$, this equals $\mathbb{E}_{u, u'}\big[\sum_{|S| \le D}\mathbb{E}_{P_u}[\chi_S]\,\mathbb{E}_{P_{u'}}[\chi_S]\big]$, an overlap expansion analogous to the Gaussian case; it is the basic computation behind low-degree bounds for planted clique and for planted constraint satisfaction problems.

## Proof sketch

The characters form an orthonormal basis of $L^2(\mathbb{Q})$, and the coefficient of $L$ on $\chi_S$ is $\mathbb{E}_{\mathbb{Q}}[L\chi_S] = \mathbb{E}_{\mathbb{P}}[\chi_S]$; projecting onto characters of degree at most $D$ and applying Parseval gives the formula. The planted form follows by writing $\mathbb{E}_{\mathbb{P}}[\chi_S]$ as an average over $u$ and expanding the square with two independent copies.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)
- [Fourier character on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/cube-chi.md)

## Proof depends on

- [Plancherel identity on the subsets of a finite set](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/fourier-plancherel.md)

## Sources

- S. B. Hopkins, "Statistical Inference and the Sum of Squares Method", PhD thesis, Cornell University (2018).
- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
