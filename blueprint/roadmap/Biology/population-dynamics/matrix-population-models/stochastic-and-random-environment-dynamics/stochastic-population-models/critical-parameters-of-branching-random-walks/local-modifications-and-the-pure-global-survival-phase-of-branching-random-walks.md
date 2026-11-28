# Local modifications and the pure global survival phase of branching random walks

**Setting.** A continuous-time branching random walk (BRW) $(X, K)$ on a countable set $X$ has particles that die at rate $1$ and each particle at $x$ places offspring at $y$ at rate $\lambda k_{xy}$; it also models an epidemic in which $\lambda k_{xy}$ is the infection rate from site $x$ to site $y$. Starting from one particle at $x$, let $\mathbf q(x, A)$ be the probability of extinction in $A \subseteq X$ (eventually no particles in $A$). The **global critical parameter** $\lambda_w(x)$ separates global extinction from global survival, and the **local critical parameter** $\lambda_s(x) \ge \lambda_w(x)$ separates almost-sure local extinction at $x$ from local survival. For irreducible BRWs these do not depend on $x$, and $(\lambda_w, \lambda_s]$ is the **pure global survival phase** (the population survives but eventually leaves every finite set). Survival in $B$ is **strong** if $\mathbf q(x, B) = \mathbf q(x, X)$.

**Theorem (local modifications).** If two BRWs $\mu, \nu$ on $X$ have the same reproduction laws outside $A$, then the probabilities of extinction before visiting $A$ coincide, $\mathbf q_0^\mu(x,A) = \mathbf q_0^\nu(x,A)$, and for every $B$, $\mathbf q^\mu(A) \le \mathbf q^\mu(B) \iff \mathbf q^\nu(A) \le \mathbf q^\nu(B)$; equality is preserved too when the laws also agree outside $B$.

**Corollary.** If $(X,K)$ and $(X,K^*)$ are irreducible and differ only on a finite set, then $\lambda^*_w < \lambda_w$, $\lambda^*_s < \lambda_w$ and $\lambda^*_w = \lambda^*_s < \lambda_w$ are equivalent; in particular, if $\min(\lambda_s, \lambda_s^*) \ge \max(\lambda_w, \lambda_w^*)$ then $\lambda_w = \lambda_w^*$.

**Proposition (no pure global survival).** If $(X,K)$ is irreducible and $\lambda_s\limsup_{x\to\infty}\sum_y k_{xy} \le 1$, then $\lambda_s = \lambda_w$.

**Proposition (maximality).** Call two irreducible BRWs equivalent, $K^* \in [K]$, if $k_{xy} = k^*_{xy}$ for all $x$ outside a finite set. If $\lambda_w^K < \lambda_s^K$, then $\lambda_w^{K^*} \le \lambda_w^K$ for every $K^* \in [K]$, and every $K^* \in [K]$ that still has a pure global survival phase has $\lambda_w^{K^*} = \lambda_w^K$. Thus, within a class of finitely modified BRWs, the global critical value cannot be raised by a local change, and it is common to all members with a pure global survival phase. For example, on the homogeneous tree $\mathbb T_d$ with $k_{xy} = 1$ on edges, $\lambda_w = 1/d < \lambda_s = 1/(2\sqrt{d-1})$.

## Proof sketch

Extinction in $A$ versus elsewhere is decided by what the process does outside $A$, because a finite modification only changes how particles reproduce while inside $A$; this is why order relations between extinction probability vectors survive local modifications. When the modification raises reproduction locally enough that the population can survive locally, it survives at a rate that is no longer tied to escape to infinity, forcing $\lambda_w^* = \lambda_s^* < \lambda_w$; otherwise the modified process inherits the original global threshold. The epidemiological reading: locally boosting transmission on finitely many sites can create local persistence, but cannot change the threshold for global spread if a pure global survival phase remains.

## Sources

- Daniela Bertacchi and Fabio Zucca, "On the Critical Parameters of Branching Random Walks", *Mathematics* 13 (2025), 2962, <https://doi.org/10.3390/math13182962>. Preprint version: arXiv:2507.14676 (2025), Definitions 2.2–2.3 (Section 2), Theorem 3.2, Corollaries 3.1–3.3 and Proposition 3.4 (Section 3), Proposition 4.1 and Example 4.2 (Section 4), <https://doi.org/10.48550/arXiv.2507.14676>.
