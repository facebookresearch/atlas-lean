# The finite-level lookdown process: consistency, exchangeability and fixed-time sampling

Let $E$ be a nonempty finite type space with its discrete sigma-algebra, $\theta\ge0$, and $h:E\times[0,1]\to E$ measurable. At every level use the same mutation operator $B\phi(x)=\frac\theta2\int_0^1(\phi(h(x,u))-\phi(x))\,du$. Initial types are independent of the future driving clocks. For $N\ge1$ and $i<j\le N$, define $S_{ij}^N x$ by copying $x_i$ into position $j$, shifting the old positions $j,\ldots,N-1$ up one position, and dropping the old position $N$. The ordered process $X^N$ on $E^N$ has generator

$$A_N f(x)=\sum_{j=1}^N B_jf(x)+\sum_{1\le i<j\le N}\bigl(f(S_{ij}^N x)-f(x)\bigr).$$

Here $B_j$ acts on coordinate $j$. Independent rate-one Poisson processes $L_{ij}$ and independent mutation Poisson measures $M_j$ of intensity $\frac\theta2\,du\,ds$ construct this process by applying their event maps chronologically. The total driving rate is $\binom N2+N\theta/2$, including events that leave the state unchanged, so the finite-state process is nonexplosive. For a real observable $\phi:E\to\mathbb R$, the coordinate equation is

$$\begin{aligned}
\phi(X_j(t))={}&\phi(X_j(0))+\int_{[0,1]\times(0,t]}[\phi(h(X_j(s-),u))-\phi(X_j(s-))]M_j(du,ds)\\
&+\sum_{i<j}\int_{(0,t]}[\phi(X_i(s-))-\phi(X_j(s-))]L_{ij}(ds)\\
&+\sum_{i<k<j}\int_{(0,t]}[\phi(X_{j-1}(s-))-\phi(X_j(s-))]L_{ik}(ds).
\end{aligned}$$

The last sum is empty when $j=1$. Using indicator observables makes this equation meaningful for categorical $E$, without subtracting type labels.

1. **Restriction consistency.** Couple systems with matching initial prefixes and the same drivers. For every $1\le n\le N$, their first $n$ coordinates agree for all times almost surely. Exchangeability is not needed for this assertion. An event with target above $n$ leaves the prefix unchanged; an event with target at most $n$ restricts to the corresponding $n$-level insertion map. Mutations obey the same restriction rule.
2. **Exchangeability and empirical path law.** If the initial vector is exchangeable, $X^N(t)$ is exchangeable for each fixed $t$. Let $Y^N$ be the unordered Moran process with the same initial law and generator

$$A_N^0f(x)=\sum_{j=1}^N B_jf(x)+\frac12\sum_{i\ne j}\bigl(f(R_{ij}x)-f(x)\bigr),$$

where $R_{ij}$ overwrites coordinate $j$ with $x_i$ and does not shift other coordinates. Then $X^N(t)$ and $Y^N(t)$ have the same law for each fixed $t$, and their entire empirical-measure processes have the same law. This does not identify their $E^N$-valued path laws. For example, with three distinct initial types, a shifting event $1\to2$ changes two coordinates at once; an unordered reproduction changes at most one.
3. **Fixed-time mixture of iid laws.** Suppose the initial finite-level laws come from conditionally iid types given a random probability law on $E$. For every fixed $t\ge0$, there is a probability law $\nu_t$ on the simplex $\mathcal P(E)$ such that, for every finite $k$,

$$\mathcal L(X_1(t),\ldots,X_k(t))=\int_{\mathcal P(E)}\mu^{\otimes k}\,\nu_t(d\mu).$$

Thus on an infinite exchangeable extension the types at this fixed time are conditionally iid given a random law. For a specified finite initial system satisfying the hypothesis, its time-$t$ law is the corresponding marginal of this representation. This is a fixed-time mixture statement, not a construction of a directing process with jointly regular paths.
4. **Finite exchangeability is insufficient.** Give $(X_1(0),X_2(0))$ the two values $(0,1)$ and $(1,0)$ with probability $1/2$ each. It is exchangeable, but its covariance is $-1/4$. For conditionally iid Bernoulli variables with directing parameter $P$, the covariance is $\operatorname{Var}(P)\ge0$. In the neutral two-level model this counterexample even has covariance $1/4-e^{-t}/2<0$ for $0\le t<\log 2$.

## Permutation coupling proof

For $N\ge2$, at reproduction times of a rate-$\binom N2$ Poisson process choose $(i,j)$ uniformly from $i<j$, independently of a fair coin. Start with an independent uniform permutation $\pi$ of the levels and put $Y_a=X_{\pi(a)}$. Exchangeability makes the initial $Y$ law equal to the initial $X$ law and independent of $\pi$. If the ordered event is $i\to j$, set $p=\pi^{-1}(i)$ and $q=\pi^{-1}(N)$. Update $\pi$ by assigning $p,q$ to $i,j$ in coin-selected order, and, for every other label $a$, keep $\pi(a)$ when it is below $j$ and increase it by one otherwise. After the ordered insertion, the corresponding update of $Y$ is exactly $Y_q\leftarrow Y_p$.

The map from the old permutation, the ordered pair and the coin to $(p,q,\pi')$ is a bijection. Its inverse takes $i=\min(\pi'(p),\pi'(q))$, $j=\max(\pi'(p),\pi'(q))$, restores $\pi(p)=i$ and $\pi(q)=N$, and undoes the shift on all other labels. Consequently $(p,q)$ is uniform on the $N(N-1)$ ordered distinct pairs and independent of the new uniform permutation. Each unordered-model directed reproduction therefore has rate $1/2$. Between reproduction events the identically distributed independent mutation drivers can be permuted with the levels. Induction over events preserves independence of $\pi_t$ from the unordered history through $t$.

The empirical measures agree pathwise in this coupling. The unordered dynamics are invariant under coordinate permutations, so their fixed-time laws are exchangeable. Applying the independent inverse permutation gives the same fixed-time law for the ordered vector. The case $N=1$ is the common mutation process.

For the mixture assertion, start the consistent family with the conditionally iid initial laws. At each fixed time, restriction consistency and exchangeability give consistent exchangeable finite-dimensional laws. Their infinite extension satisfies the finite-alphabet de Finetti theorem, yielding $\nu_t$. De Finetti's theorem for binary sequences alone does not give the finite-alphabet case.

## Related topics

- [Moran model](../../moran-model/README.md)

## Scope

This is the finite-type, shifting/inserting construction. Etheridge's non-shifting copying convention is a different event map; its Kingman genealogical comparison is treated separately. A fixed-$N$ empirical frequency process is grid-valued with jump paths, not the Wright–Fisher diffusion. No infinite-level path construction, simultaneous-in-time directing law, empirical path convergence, or Fleming–Viot martingale problem is asserted here. A proof page must still supply de Finetti's theorem for a finite alphabet and the identification of the construction with the path of a finite continuous-time Markov chain. The related lookdown overview covers the finite construction and exchangeability scope.

## Sources

- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, <https://www.staff.uni-mainz.de/birkner/SPM2526/StochPopModels_25-26.pdf>, Sec. 1.5, (1.25)–(1.29), Lemma 1.5.1 and its permutation proof (1.30)–(1.34); Remark 1.5.4 for the fixed-time de Finetti step.
- A. Etheridge, *Diffusion process models in mathematical genetics*, lecture notes, Definition 2.1 and Remark 2.2, for comparison with the non-shifting convention only.
