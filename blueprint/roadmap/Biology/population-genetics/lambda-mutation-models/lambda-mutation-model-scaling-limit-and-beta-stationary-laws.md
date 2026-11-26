# Λ-mutation model: consistency, scaling limit and beta stationary laws

**Model.** Fix $N \in \mathbb{N}$ and a finite measure $\Lambda$ on $[0,1]$. A population of $N$ individuals carries two types; let $X^{(N)}_t \in \{0, \dots, N\}$ be the number of type-1 individuals. Groups of individuals of the same type mutate *simultaneously* to the other type: the generator is
$$L^{X^{(N)}} f(n) = \sum_{k=1}^n \varphi(k,n)\big(f(n-k) - f(n)\big) + \sum_{k=1}^{N-n} \varphi(k, N-n)\big(f(n+k) - f(n)\big),$$
where a given block of $n$ same-type individuals loses $k$ of them at rate $\varphi(k,n)$, with
$$\varphi(k,n) = \binom{n}{k}\int_{[0,1]} t^{k-1}(1-t)^{n-k}\,\Lambda(dt), \qquad 1 \le k \le n.$$

**Consistency.** For a nonnegative triangular array $(\varphi(k,n))$, the following are equivalent: (i) the sampling-consistency relations
$$\varphi(k,n) = \Big(1 - \frac{k}{n+1}\Big)\varphi(k,n+1) + \frac{k+1}{n+1}\varphi(k+1,n+1)$$
hold for all $n \in \mathbb{N}$, $1 \le k \le n$; (ii) $\varphi$ has the integral representation above for some finite $\Lambda$; (iii)–(iv) the two-type and one-type generators commute with the operator that removes one individual uniformly at random. So the model is the mutation analogue of a $\Lambda$-coalescent: dropping a random individual from $N+1$ gives the size-$N$ model.

**Theorem (scaling limit).** If $X_0^{(N)}/N \to X_0$ in law, then $(X^{(N)}_t / N)_{t \ge 0}$ converges in $D_{[0,1]}[0,\infty)$ to the Markov process $X$ on $[0,1]$ with generator
$$L^X f(x) = \Lambda(\{0\})(1 - 2x) f'(x) + \int_{(0,1]} \big(f(x(1-t)) + f(x(1-t) + t) - 2 f(x)\big)\frac{\Lambda(dt)}{t}, \qquad f \in C^2([0,1]).$$
An atom at $0$ gives symmetric linear mutation drift; mass at $t > 0$ makes a fraction $t$ of each type flip at once.

**Proposition (beta mutation measure).** Let $\Lambda = \mathrm{Beta}(a,b)$ with $a, b > 0$. Then
1. the stationary distribution $\mu$ of $X$ is a beta distribution if and only if $a \in \{1, 2\}$ or $a = b$, and in that case $\mu = \mathrm{Beta}(b/a, b/a)$;
2. $\mu$ is reversible for $X$ if and only if $a = 1$.

## Expansion

The consistency relation says a group of $k$ simultaneous mutants among $n+1$ individuals, after deleting a uniformly chosen individual, is either still $k$ mutants (if a non-mutant was deleted) or $k$ mutants from $k+1$; the de Finetti/Hausdorff moment argument that gives Pitman's $\Lambda$-coalescent representation gives the integral form here. Under scaling, $\varphi(k,n)/n$ with $k \approx t n$ becomes $\Lambda(dt)/t$ applied to each type separately, hence the two symmetric jump terms. The stationary law is identified through an integral equation for its moment generating function and a moment duality $\mathbb{E}_x[X_t^n]/\mu_n$ with a pure death process; for the beta family the equation closes on beta moments exactly in the stated cases.

## Sources

- Cristian Giardinà and Martin Möhle, "On a Λ-mutation model and the harmonic model", arXiv:2606.00781 (2026), Proposition "Consistency", Theorem "Scaling limit for $X^{(N)}/N$" and Proposition "Stationary distribution of the beta-mutation model", <https://doi.org/10.48550/arXiv.2606.00781>.
