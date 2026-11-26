# Time-changed Λ-coalescent limits of modified Moran models

**Setting.** A Cannings model with variable population sizes $(N_r)_{r\in\mathbb{N}_0}$ (generation $r$ counted backward from the sampling generation, $N = N_0$) has exchangeable offspring numbers in every generation. Let $c_{N,r}$ be the probability that two individuals of generation $r-1$ share a parent in generation $r$, let $c_N$ be the pair-coalescence probability of the fixed-size model, and let $(\tilde{\mathcal{R}}^{(N)}_r)_{r\ge 0}$ be the ancestral partition of a sample of $n$ individuals. A *population size profile* is a positive function $\nu$ with

$$c_1(t)N \le N_r \le c_2(t)N \ \ (r \le c_N^{-1}t), \qquad N^{-1}N_{\lfloor t c_N^{-1}\rfloor} \to \nu(t) \quad (N \to \infty).$$

In a **modified Moran model** of size $N$, in each generation one uniformly chosen parent has $U_N \in \{2,\dots,N\}$ offspring, $U_N - 1$ others have none and the remaining $N - U_N$ have one each. For a probability measure $\Lambda$ on $[0,1]$, let $U'_N$ have the law of the size of the first merger of a $\Lambda$-$N$-coalescent,

$$P(U'_N = j) = \lambda_N^{-1}\binom{N}{j}\,E\big(X^{j-2}(1-X)^{N-j}\big), \quad j \ge 2,\ X \sim \Lambda,$$

where $\lambda_N$ is the total merger rate. Size changes between generations are realized by sampling offspring without replacement (decline) or by giving the extra offspring to the multiplying parent or to formerly childless parents (growth), so each generation remains a modified Moran model.

**Theorem.**

1. *(Thinned case.)* Suppose $E((U'_N)_2)/(N-1) \not\to 0$. Put $U_N = U'_N\mathbf{1}_{A_N} + 2(1-\mathbf{1}_{A_N})$ with $A_N$ independent of $U'_N$ and $E((U'_N)_2)P(A_N)/(N)_2 = N^{-\gamma}$ for some $1 < \gamma < 2$. For every profile $\nu$ there are admissible sizes $(N_r)$ such that, in the Skorokhod sense,

$$\big(\tilde{\mathcal{R}}^{(N)}_{[c_N^{-1}t]}\big)_{t\ge0} \xrightarrow{d} \big(\Pi_{\mathcal{G}(t)}\big)_{t\ge0}, \qquad \mathcal{G}(t) = \int_0^t \nu(s)^{-\gamma}\,ds,$$

where $\Pi$ is the $\Lambda$-$n$-coalescent.

2. *(Unthinned case.)* Suppose $E((U'_N)_2)/(N-1) \to 0$ and take $U_N = U'_N$. For every $\nu$ there are admissible sizes such that $\tilde{\mathcal{R}}^{(N)}$, run on the generation scale $\mathcal{G}_N^{-1}(t) = \inf\{s > 0 : \sum_{r=1}^{[s]} c_{N,r} > t\} - 1$, converges to the $\Lambda$-$n$-coalescent itself.

3. *(Beta coalescents.)* If $\Lambda = \mathrm{Beta}(a,b)$ with $a \in (0,1)$, $b > 0$, the time change can be moved to the limit: for every $\nu$, $\tilde{\mathcal{R}}^{(N)}_{[c_N^{-1}t]}$ converges to $\Pi_{\mathcal{G}(t)}$ with $\mathcal{G}(t) = \int_0^t \nu(s)^{a-2}\,ds$. The same holds for $a \in (1,2)$ under exponential growth $\nu(t) = e^{-\rho t}$.

4. *(Moran model.)* For the standard Moran model and any profile $\nu$, the genealogy converges to Kingman's $n$-coalescent time-changed by $\mathcal{G}(t) = \int_0^t \nu(s)^{-2}\,ds$.

## Depends on

- [Cannings model of a haploid population](../multiple-merger-coalescents/cannings-models/cannings-model.md)

## Expansion

The proof adapts Möhle's sufficient condition for convergence of Cannings genealogies: if the one-generation merger probabilities with variable sizes satisfy $\Phi^{(N)}_l(r;a_1,\dots,a_l) = \Phi^{(N_r)}_l(a_1,\dots,a_l) + o_{\Sigma}(c_{N_r})$ (an error that stays negligible after summing over the $O(c_N^{-1})$ generations of one coalescent time unit), then the genealogy converges to the $\Lambda$-coalescent run at the accumulated coalescence probability $F_N(s) = \sum_{r\le s} c_{N,r}$. The allocation scheme for added individuals is chosen so that each generation's merger probabilities are those of a fixed-size model of size $N_r$. When $c_N$ is regularly varying, $c_N \approx cN^{-\gamma}$, one has $c_{N,r}/c_N \approx (N_r/N)^{-\gamma} \to \nu(t)^{-\gamma}$, which turns the generation clock into the deterministic time change $\mathcal{G}$; for $\mathrm{Beta}(a,b)$ coalescents $\gamma = 2-a$ and for the Moran model $\gamma = 2$.

## Sources

- Fabian Freund, "Cannings models, population size changes and multiple-merger coalescents", arXiv:1902.02155 (2019), Section 2, Theorems 2.1 and 2.2, Corollaries 2.4 and 2.5, Proposition 2.6, <https://doi.org/10.48550/arXiv.1902.02155>.
