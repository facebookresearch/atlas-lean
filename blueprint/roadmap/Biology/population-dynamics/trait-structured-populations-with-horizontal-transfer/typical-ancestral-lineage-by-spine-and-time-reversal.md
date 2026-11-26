# Typical ancestral lineage of a non-stationary population via spine and time reversal

**Setting.** Let $\xi_t(x)$ be the deterministic large-population density of a trait-structured population on $[0,T]$, with total mass $\lambda_t = \int \xi_t$, and freeze the interactions along it: each individual then evolves independently, with net growth rate $r^\lambda(s,x) = b(x) - d(x) - C\lambda_s$ and trait motion (variation and transfer from the frozen population) given by a time-inhomogeneous jump generator $Q$. Let $X$ be the Markov process with generator $Q$ and define the Feynman–Kac semigroup
$$\widehat{P}_t\varphi(s,x) = \mathbb{E}\Big[e^{\int_0^t r^\lambda(s+u, X_{s+u})\,du}\,\varphi(s+t, X_{s+t}) \,\Big|\, X_s = x\Big],$$
which equals the expected value of $\langle \delta_{s+t}\otimes \widehat{Z}_{s+t}, \varphi\rangle$ for the linearized (branching) population started from one individual at $(s,x)$. Put $m_T(s,x) = \widehat{P}_{T-s}1(s,x)$.

**Proposition (spine).** The $h$-transformed semigroup
$$\widetilde{P}_t\varphi(s,x) = \frac{\widehat{P}_t(\varphi\, m_T)(s,x)}{m_T(s,x)}, \qquad 0 \le s \le s+t \le T,$$
is the semigroup of a time-inhomogeneous Markov process $(Y_t)_{t\in[0,T]}$ (the spine), and when $Y_0$ has law $m_T(0,x)\xi_0(x)\,dx/\langle\xi_T,1\rangle$, the law of $Y_t$ has density $m_T(t,x)\,\xi_t(x)/\langle\xi_T,1\rangle$.

**Theorem (law of a typical ancestral lineage).** Under the hypotheses of the large-population limit, with $Z^K_0 \to \xi_0(x)dx$, let $H^K_T$ be the historical process (trait paths of the individuals alive at $T$) and $\mathcal{R}$ the path reversal $s \mapsto T - s$. For every bounded measurable path functional $\Phi$,
$$\lim_{K\to\infty}\mathbb{E}\left[\frac{\langle H^K_T, \Phi\circ\mathcal{R}\rangle}{\langle H^K_T, 1\rangle}\right] = \mathbb{E}_{\xi_T}\big[\Phi(\mathcal{R}(Y))\big],$$
where $\mathcal{R}(Y)$ is the Markov process with semigroup $\widetilde{P}^{\mathcal{R}}_t\psi(s,x) = \xi(s,x)^{-1}\,\widetilde{P}'_t(\xi\psi)(s,x)$, $0 \le t \le s \le T$, and $\widetilde{P}'$ is the dual of $\widetilde{P}$ with respect to $\xi(s,x)\,ds\,dx$. So the trait path of the ancestry of an individual sampled uniformly at time $T$ is, in the limit, the time reversal of the spine started from $\xi_T$.

## Depends on

- [Large-population limit of a trait-structured population with horizontal transfer](large-population-limit-with-frequency-dependent-transfer.md)

## Expansion

A many-to-one formula identifies the trait of a uniformly sampled individual's ancestor with the spine, the process tilted by the expected number of descendants alive at $T$, $m_T$. Replacing the interacting process by the branching process in the frozen environment costs nothing in the limit because both converge to $\xi$ in $L^2$. Nagasawa's theorem gives the reversed semigroup through the duality $\int P_t\varphi\,\psi\,d\eta = \int \varphi\,S_t\psi\,d\eta$ with the excessive measure $\eta$, here $\xi(s,x)\,ds\,dx$; the novelty is that $\xi$ is not stationary, so the reversal is time-inhomogeneous and requires regularity of the series representation of the semigroups in $s$.

## Sources

- M. Deangeli Bravo, "Ancestral lineages under horizontal trait transfer: spinal decomposition and time reversal beyond stationarity", arXiv:2609.39270 (2026), Propositions 3.4, 3.7, 3.11, Theorem 5.4 and Theorem 10.2, <https://doi.org/10.48550/arXiv.2609.39270>.
