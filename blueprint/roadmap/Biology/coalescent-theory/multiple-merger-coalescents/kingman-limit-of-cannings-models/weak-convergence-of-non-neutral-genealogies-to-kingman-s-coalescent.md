# Weak convergence of non-neutral genealogies to Kingman's coalescent

**Setting.** $N$ particles reproduce in discrete generations, labelled backwards in time ($0$ is the present). Particle $j$ in generation $t-1$ has parent $a^{(j)}_t\in[N]$ in generation $t$, and $\nu^{(i)}_t=\#\{j:a^{(j)}_t=i\}$ are the offspring counts, which may depend on the whole history (selection, fitness inheritance, sequential Monte Carlo resampling). Let $\mathcal F_t=\sigma(\nu^{(1:N)}_s,s\le t)$. Assume the *random assignment condition* (A1): given $\nu^{(1:N)}_t$, parental indices are uniform over all assignments with these counts (weaker than exchangeability). Sample $n$ particles at time $0$ and let $G^{(n,N)}_t\in\mathcal P_n$ be the partition of $[n]$ into groups with a common ancestor $t$ generations back. Define the random pair-merger probability and time change

$$c_N(t)=\frac1{(N)_2}\sum_{i=1}^N(\nu^{(i)}_t)_2,\qquad \tau_N(t)=\inf\Big\{s\in\mathbb N:\sum_{r=1}^sc_N(r)\ge t\Big\},$$

where $(x)_k=x(x-1)\cdots(x-k+1)$.

**Theorem.** Suppose (A1), that $\mathbb P[\tau_N(t)=\infty]=0$ for all $t$ and large $N$, and that there is a deterministic $b_N\to0$ with, almost surely and uniformly in $t\ge1$,

$$\frac1{(N)_3}\sum_{i=1}^N\mathbb E\big[(\nu^{(i)}_t)_3\mid\mathcal F_{t-1}\big]\le b_N\,\frac1{(N)_2}\sum_{i=1}^N\mathbb E\big[(\nu^{(i)}_t)_2\mid\mathcal F_{t-1}\big].$$

Then the rescaled genealogy $(G^{(n,N)}_{\tau_N(t)})_{t\ge0}$ converges weakly in the Skorokhod space $\mathcal D([0,\infty),\mathcal P_n)$ to Kingman's $n$-coalescent as $N\to\infty$.

## Depends on

- [Path-level convergence of rescaled ancestral partition chains in Skorokhod space](path-level-convergence-of-rescaled-ancestral-par.md)
- [Möhle–Sagitov conditions for a Kingman genealogy limit](mohle-sagitov.md)

## Expansion

Under neutrality the offspring counts are independent of the past and the classical Möhle–Sagitov argument applies. With selection, offspring counts are correlated across generations through inherited fitness, so the merger rates form a random environment; the time change by the *random* $c_N(t)$ (rather than its expectation) absorbs this. Conditionally on the offspring counts, the genealogical chain has one-step identity probabilities $p_{\xi\xi}(t)$ squeezed between $1-\binom{|\xi|}2\big(c_N(t)+B_{|\xi|}D_N(t)\big)(1+O(N^{-1}))$ and $1-\binom{|\xi|}2\big(c_N(t)-B'_{|\xi|}D_N(t)\big)(1+O(N^{-1}))$, with $D_N(t)=\frac1{N(N)_2}\sum_i(\nu^{(i)}_t)_2\big(\nu^{(i)}_t+\frac1N\sum_{j\ne i}(\nu^{(j)}_t)^2\big)$ controlling multiple and simultaneous mergers. The third-moment condition makes $D_N$ negligible against $c_N$, so the conditional chain is coupled with a Kingman coalescent run on the random clock; finite-dimensional convergence plus tightness (few mergers in short windows) yields weak convergence of whole paths. Applications include the full genealogical tree of interacting particle filters, whose ancestral degeneracy is governed by $c_N$.

## Sources

- Suzie Brown, Paul A. Jenkins, Adam M. Johansen and Jere Koskela, "Weak convergence of non-neutral genealogies to Kingman’s coalescent", Stoch. Process. Appl. 162 (2023), 76–105, <https://doi.org/10.1016/j.spa.2023.04.016>. Numbering follows the arXiv version, arXiv:2110.05356 (2021): Section 2 (assumption (A1), definitions of $c_N$, $\tau_N$, $D_N$, Propositions 1–3) and Section 3 (Theorem 1), <https://doi.org/10.48550/arXiv.2110.05356>.
