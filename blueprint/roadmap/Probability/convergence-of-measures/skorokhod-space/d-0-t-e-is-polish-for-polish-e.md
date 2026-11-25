# D([0,T],E) is Polish for Polish E

Let $(E,r)$ be a Polish space, with $r$ a complete separable metric, and $T>0$. Then the [Skorokhod space](skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md) $D([0,T],E)$ with the J1 topology is separable, and it admits a complete metric $d^\circ$ that induces the J1 topology: with

$$\|\lambda\|^\circ=\sup_{0\le s<t\le T}\Bigl|\log\frac{\lambda(t)-\lambda(s)}{t-s}\Bigr|,\qquad d^\circ(x,y)=\inf_{\lambda\in\Lambda_T}\max\Bigl(\|\lambda\|^\circ,\ \sup_{t\in[0,T]}r\bigl(x(t),y(\lambda(t))\bigr)\Bigr),$$

where $\Lambda_T$ is the set of increasing homeomorphisms of $[0,T]$. Hence $D([0,T],E)$ is a Polish space. For $E=\mathbb R$ this gives completeness and separability of the Skorokhod space of real paths.

## Depends on

- [Skorokhod space D([0,T],E) for a metric space E: J1 topology and embeddings](skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md)

## Expansion

A full page must establish that $d^\circ$ is a metric, that $d$ and $d^\circ$ have the same convergent sequences, completeness of $d^\circ$ (a $d^\circ$-Cauchy sequence has a subsequence with summable time changes whose composition converges), and separability from a countable dense set of step paths with rational jump times and values in a countable dense subset of $E$. The case $E=\mathbb R$ should be stated as a corollary. Since $D([0,T],E)$ is Polish, Prokhorov's theorem on Polish spaces identifies tight families of laws on $D([0,T],E)$ with relatively compact ones; the [real-line form](../prokhorov-theorem/prokhorov-sequential.md) is the case of $\mathbb R$ only, so this consequence needs the Polish-space form.

## Sources

- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley (1999), <https://en.wikipedia.org/wiki/Convergence_of_Probability_Measures> (book description), Chapter 3 (separability and completeness of $D$; the metric $d^\circ$).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), Chapter 3, Section 5 ($D_E[0,\infty)$ is separable and complete for separable complete $E$).
