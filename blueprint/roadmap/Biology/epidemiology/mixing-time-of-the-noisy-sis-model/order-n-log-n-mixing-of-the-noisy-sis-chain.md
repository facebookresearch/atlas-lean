# Order n log n mixing of the noisy SIS chain

**Model.** On a graph $G_n=(V_n,E_n)$ with $n$ vertices and maximum degree $\Delta^{(n)}_{\max}$, a configuration $\sigma\in\{0,1\}^{V_n}$ marks infected vertices. For $x\in V_n$ let $n_{I,\sigma}(x)$ be its number of infected neighbours and
$$p(\sigma,x)=a+\lambda\,n_{I,\sigma}(x),\qquad a,\lambda,\kappa>0,\quad a+\lambda\Delta^{(n)}_{\max}<1 .$$
At each discrete step a uniform vertex $x$ is chosen: if susceptible it becomes infected with probability $p(\sigma,x)$ ($a$ is the external infection probability), and if infected it recovers with probability $\kappa$. Because $a>0$ the chain is irreducible with a unique stationary law $\mu^{(n)}_{a,\lambda,\kappa}$; $t^{(n)}_{\rm mix}(\epsilon)$ is its total-variation mixing time.

**Upper bound.** If there is $\gamma\in(0,1)$, independent of $n$, with $|p(\sigma,x)-\kappa|\ge\gamma$ for all $\sigma,x$ and $\lambda\Delta^{(n)}_{\max}<\gamma$, then for every $\epsilon\in(0,1)$ and large $n$,
$$t^{(n)}_{\rm mix}(\epsilon)\le\frac{n}{\gamma-\lambda\Delta^{(n)}_{\max}}\big(\log n+\log(1/\epsilon)\big).$$

**Lower bound.** If the chain is attractive, $a+\lambda\Delta^{(n)}_{\max}\le1-\kappa$, then $t^{(n)}_{\rm mix}(\epsilon)\ge(1-o(1))\,n\log n$.

**Stationary law.** For every $S\subseteq V_n$, $\mu^{(n)}(\sigma_x=0\ \forall x\in S)\le(1-p^\star)^{|S|}\le e^{-p^\star|S|}$ with $p^\star=a/(a+\kappa)$.

**Random graphs.** With high probability over the graph, the $\Theta(n\log n)$ mixing holds on Erdős–Rényi graphs with $np\gg\log n$ when either $\kappa\le a-\gamma$ and $\lambda np\le\min\{\gamma,1-a-\kappa\}-\iota$, or $\lambda np\le\min\{\gamma,\kappa-a-\gamma,1-\kappa-a\}-\iota$, for some $\iota>0$; on random $d$-regular multigraphs with $\lambda d$ in place of $\lambda np$; and on Galton–Watson trees with $\lambda(1+C\log n/\log\log n)$ in place of $\lambda np$, reflecting the maximal degree of such trees.

## Expansion

Upper bound by coupling: run two copies with the same vertex choice and the same uniform variable for each update. A discrepancy at the chosen vertex is removed with probability at least $\gamma$, while an update of one of its neighbours creates a new discrepancy with probability at most $\lambda$, so the expected Hamming distance contracts by a factor $1-(\gamma-\lambda\Delta_{\max})/n$ per step and the copies coalesce after $O(n\log n)$ steps. The lower bound uses attractiveness (the update is monotone in the configuration) to compare with the non-interacting chain through a monotone coupling in $\lambda$; for independent sites, order $n\log n$ steps are needed before every vertex has been updated. On random graphs the typical maximum degree replaces $\Delta_{\max}$.

## Sources

- W. R. KhudaBukhsh, Y. Xiang, "Mixing time for an epidemic model on graphs with external sources of infection", arXiv:2501.07738 (2025), model (transition rules), Assumptions of uniform gap and attractiveness, Theorems 1–6, Corollary 1, <https://doi.org/10.48550/arXiv.2501.07738>.
