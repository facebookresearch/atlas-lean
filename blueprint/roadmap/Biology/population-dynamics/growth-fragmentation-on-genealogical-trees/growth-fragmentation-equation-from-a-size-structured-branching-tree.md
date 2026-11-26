# Growth-fragmentation equation from a size-structured branching tree

**Model.** Each cell $u$ of a binary genealogical tree is born with size $\xi$ and an individual growth rate $\tau_u = v \in \mathcal{E}$, a compact subset of $(0,\infty)$. During its life its size grows exponentially, $\dot x = v x$, and it divides at size-dependent rate $B(x)$ into two daughters of half its size. Each daughter draws its growth rate from a Markov kernel $\rho(v,dv')$ given its mother's rate. Assume $B$ is continuous, $B(0) = 0$ and $\int^\infty x^{-1}B(x)\,dx = \infty$, so every cell divides in finite time. Under these assumptions the piecewise deterministic Markov branching process is well defined, with almost surely no accumulation of division times.

**Theorem (mean empirical measure).** Let $\mu$ be the initial law of $(\text{size}, \text{growth rate})$ of the ancestor, and define $n(t,dx,dv)$ by

$$ \langle n(t,\cdot),\varphi\rangle = \mathbb{E}_\mu\Big[\sum_i \varphi\big(X_i(t),V_i(t)\big)\Big] $$

over all cells alive at time $t$. Then $n$ is a weak solution of the growth-fragmentation equation with variable growth rate

$$ \partial_t n(t,x,v) + v\,\partial_x\big(x\,n(t,x,v)\big) + B(x)\,n(t,x,v) = 4B(2x)\int_{\mathcal{E}}\rho(v',v)\,n(t,2x,dv'), \qquad n(0,\cdot) = \mu . $$

**Proposition (division rate from the tree's invariant law).** Let $\mathcal{P}_B$ be the Markov chain of (birth size, growth rate) along a line of descent. If it has an invariant probability $\nu_B(x,dv)\,dx$ with size marginal $\nu_B(y)$, then

$$ \nu_B(y) = \frac{B(2y)}{y}\,\mathbb{E}_{\nu_B}\Big[\frac{1}{\tau_{u^-}}\mathbf{1}_{\{\xi_{u^-} \le 2y,\ \xi_u \ge y\}}\Big], $$

where $u^-$ is the parent of $u$. Hence $B$ can be read off from birth sizes and growth rates observed along the tree.

## Expansion

The PDE is the forward (Kolmogorov) equation of the branching process. Transport $v\partial_x(xn)$ comes from exponential growth, loss $Bn$ from division, and the gain term $4B(2x)n(2x)$ has one factor $2$ for the two daughters and another for the Jacobian of halving. The representation of $\nu_B$ follows from the transition kernel of birth sizes: a cell born at size $\xi_{u^-}$ with rate $\tau_{u^-}$ divides at size $2y$ with density $\frac{B(2y)}{\tau_{u^-}2y}\exp\big(-\int_{\xi_{u^-}}^{2y}\frac{B(s)}{\tau_{u^-}s}ds\big)$. Integrating against $\nu_B$ and using invariance turns the survival factor into the indicator $\{\xi_{u^-} \le 2y,\ \xi_u \ge y\}$. A many-to-one formula through a tagged cell links tree averages to this single-lineage chain.

## Sources

- Marie Doumic, Marc Hoffmann, Nathalie Krell and Lydia Robert, "Statistical estimation of a growth-fragmentation model observed on a genealogical tree", arXiv:1210.3240 (2012), Section 2, Assumption 1, Proposition 1 and Theorem 1; Section 3, Proposition 2; Section 5, Proposition 3 (many-to-one formula), <https://doi.org/10.48550/arXiv.1210.3240>.
