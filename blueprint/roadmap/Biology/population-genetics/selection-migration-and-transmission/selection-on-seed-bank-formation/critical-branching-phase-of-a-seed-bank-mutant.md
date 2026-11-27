# Critical branching phase of a seed-bank mutant

**Model.** In a Wright–Fisher population of $N$ annual plants, each wild-type plant contributes $\mathrm{Poisson}(M)$ seeds to the pool that germinates next generation, while each mature mutant plant of generation $t-i$ contributes $\mathrm{Poisson}(Mb_i)$ seeds to that pool, $i=0,\dots,K$, where

$$\sum_{i=0}^K b_i=1,\qquad b_0>0,\qquad B:=\sum_{i=1}^K i\,b_i$$

($B$ is the mean germination time). The next generation is $N$ seeds sampled from the pool. While mutants are rare, the mutant family is approximated by a multitype branching process $\mathbf Z(t)=(Z_0(t),\dots,Z_K(t))$, where $Z_0$ counts mature mutants and $Z_i$ ($i\ge1$) counts mutant seeds that will germinate $i$ generations later.

**Theorem.** Started from one mature mutant, $\mathbf Z$ is critical and

$$\lim_{t\to\infty}t\,\mathbb P_{\mathbf e_0}(\mathbf Z(t)\neq0)=2(B+1).$$

Conditional on survival, the number of mature mutants is asymptotically exponential:

$$\lim_{t\to\infty}\mathbb P_{\mathbf e_0}\!\Big(\tfrac{Z_0(t)}{t}\ge y\ \Big|\ \mathbf Z(t)\ne0\Big)=e^{-2y(B+1)^2},\qquad y\ge0 .$$

**Correspondence with a neutral allele.** For $B\ge0$ and small $y$, the frequency reached by the seed-bank mutant at the end of the branching phase that corresponds to frequency $y$ of a neutral allele without seed bank is

$$\psi_B(y)=\frac{1}{2(B+1)^2}\log\frac{B+1}{B+e^{-2y}},$$

which is strictly increasing in $y$ and strictly decreasing in $B$, with $\psi_0(y)=y$.

## Proof depends on

- [Mean identity for multitype Galton–Watson processes](../../../../Probability/branching-processes/galton-watson-process/multitype-galton-watson-processes.md)

## Proof idea

Each mutant seed eventually germinates with total mean offspring $\sum_i b_i=1$, so the mean matrix has Perron root $1$ (criticality). For a critical multitype Galton–Watson process, Kolmogorov–Yaglom asymptotics give survival $\sim 2/(t\,Q)$ and an exponential conditional limit, where $Q$ is the offspring variance projected on the left and right Perron eigenvectors. Here the right eigenvector weighs a seed by the time it still has to wait, and the normalization introduces the factor $B+1$, the mean generation length. Since a seed-bank family spends a fraction $B/(B+1)$ of its mass dormant, it reaches fewer mature plants at a given time than a neutral family, which is why $\psi_B(y)<y$ for $B>0$.

## Sources

- A. Etheridge and J. L. de Oliveira Madeira, "How seed banks evolve in plants: a stochastic dynamical system subject to a strong drift", Electronic Journal of Probability 31 (2026), 1–82, <https://doi.org/10.1214/26-EJP1596>. Numbering as in the preprint arXiv:2602.04437v1, <https://arxiv.org/abs/2602.04437v1>: Section 2.1, Theorem 2.1 and Lemma 2.2.
